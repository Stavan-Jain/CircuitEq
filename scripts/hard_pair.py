#!/usr/bin/env python3
"""A Clifford+T pair built to sit past every published equivalence checker, and a ladder.

`docs/tool-survey.md` explains the design; `benchmarks/hard_pair/README.md` has the
ladder's results. Circuit A has `rounds` rounds on `n` wires. A round is a CX on every
pair of a random perfect matching (random orientation), then on every wire one of H, S,
T or Tdg, or nothing, with probability 1/4 each (T and Tdg share their quarter).

Circuit B is the same unitary up to a global phase, in Pauli-rotation form:

1. Every T of A is pushed to the front through the Clifford gates before it, with a
   tableau that keeps exact signs: `A = D · R_m ⋯ R_1`, where `D` is A's Clifford
   skeleton and `R_j = exp(-i k_j π/8 P_j)` for a Pauli `P_j` that is dense after a few
   rounds.
2. `nests` spider nests are inserted: 15 rotations of angle `±π/8` about the nonempty
   products of 4 commuting Paulis, with signs `(-1)^(|S|+1)`. Their product is a global
   phase, because the phase function is `8·x1·x2·x3·x4 = 0 (mod 8)`. Each nest is
   hosted at a T of A, with its 4 Paulis the frame images of that T's wire and three
   other wires of the same round, so its singletons merge into A's rotations.
3. Rotations about equal Paulis are merged through commuting neighbours, and commuting
   neighbours are shuffled.
4. Each rotation is emitted as a basis change, a CNOT ladder (star or chain), a phase
   and their inverses. `D` is re-synthesised from its tableau by elimination.
   Adjacent inverse pairs are then cancelled.

B shares no gate positions with A. Two mutants, each B with one rotation negated
(one gate differs from B, T for Tdg or S for Z), are not equivalent to A: B- negates a
nest rotation with X or Y on some wire from the second half of B, so it differs by a
Clifford π/4 rotation about a dense Pauli, conjugated; B-diag negates a diagonal
rotation with only diagonal rotations before it, so the difference is a diagonal phase
that no computational-basis stimulus can see.

Every step is an exact identity, so equivalence holds by construction; `--self-test`
(CI) checks it on dense unitaries for small `n`, and cross-reads the QASM with PyZX when
it is importable. Generation is standard library only and deterministic in the seed.
The dense and stimulus checkers need numpy; the others need pyzx, quizx and mqt.qcec,
which the harness env `envs/qcec` has (`uv venv --python 3.12 ~/.circuiteq-harness/envs/qcec`,
then `uv pip install --python ~/.circuiteq-harness/envs/qcec/bin/python mqt.qcec==3.10.0
quizx==0.3.0 pyzx==0.9.0 numpy`).

    PY=~/.circuiteq-harness/envs/qcec/bin/python
    $PY scripts/hard_pair.py --self-test
    $PY scripts/hard_pair.py make --n 64 --out /tmp/hp64
    $PY scripts/hard_pair.py ladder --rungs 8,12,16,24,32,40,64 --timeout 300
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
import random
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from alphabet import FROM_QASM, INVERSE, PHASES, TO_QASM  # noqa: E402

# The QASM name each written gate inverts to, for the quizx checker's miter.
QASM_INVERSE = {TO_QASM[g]: TO_QASM[INVERSE[g]] for g in TO_QASM} | {"cx": "cx"}
HARNESS_HOME = Path(os.environ.get("CIRCUITEQ_HARNESS_HOME", "~/.circuiteq-harness")).expanduser()

# A gate is (name, wire) or ("CX", control, target); circuits are lists in time order.


def bits(v: int):
    """The set bits of `v`, lowest first."""
    while v:
        low = v & -v
        yield low.bit_length() - 1
        v ^= low


# --- Pauli strings --------------------------------------------------------------------
# (x, z, r) is i^r · Π_j X_j^{x_j} Z_j^{z_j}, with X before Z on each wire.

def pmul(a, b):
    """The product a·b, phase exact."""
    return (a[0] ^ b[0], a[1] ^ b[1], (a[2] + b[2] + 2 * (a[1] & b[0]).bit_count()) % 4)


def commute(a, b) -> bool:
    """Whether the Paulis with masks a[:2] and b[:2] commute."""
    return ((a[0] & b[1]).bit_count() + (a[1] & b[0]).bit_count()) % 2 == 0


def conj(g, p):
    """g p g† for a Clifford gate g."""
    x, z, r = p
    if g[0] == "CX":
        c, t = g[1], g[2]
        return (x ^ (((x >> c) & 1) << t), z ^ (((z >> t) & 1) << c), r)
    name, q = g
    a, b = (x >> q) & 1, (z >> q) & 1
    if name == "H":
        if a != b:
            x ^= 1 << q
            z ^= 1 << q
        return (x, z, (r + 2 * (a & b)) % 4)
    if name == "S":
        return (x, z ^ (a << q), (r + a) % 4)
    if name == "Sdg":
        return (x, z ^ (a << q), (r + 3 * a) % 4)
    if name == "X":
        return (x, z, (r + 2 * b) % 4)
    if name == "Z":
        return (x, z, (r + 2 * a) % 4)
    raise ValueError(f"not a Clifford gate: {g}")


def signed(p):
    """(x, z, s) with p = s · i^{|x∧z|} X^x Z^z, the Hermitian Pauli with sign s = ±1."""
    x, z, r = p
    d = (r - (x & z).bit_count()) % 4
    if d not in (0, 2):
        raise ValueError(f"not Hermitian: {p}")
    return x, z, 1 if d == 0 else -1


class Frame:
    """The images Φ(X_q), Φ(Z_q) of P ↦ D† P D, for the Clifford gates D seen so far."""

    def __init__(self, n: int):
        self.X = [(1 << q, 0, 0) for q in range(n)]
        self.Z = [(0, 1 << q, 0) for q in range(n)]

    def append(self, g):
        """D ← g·D, i.e. Φ ← Φ(g† · g)."""
        if g[0] == "CX":
            c, t = g[1], g[2]
            self.X[c] = pmul(self.X[c], self.X[t])
            self.Z[t] = pmul(self.Z[c], self.Z[t])
            return
        name, q = g
        if name == "H":
            self.X[q], self.Z[q] = self.Z[q], self.X[q]
        elif name in ("S", "Sdg"):          # S†XS = -iXZ, SXS† = iXZ
            x = pmul(self.X[q], self.Z[q])
            self.X[q] = (x[0], x[1], (x[2] + (3 if name == "S" else 1)) % 4)
        elif name == "X":
            z = self.Z[q]
            self.Z[q] = (z[0], z[1], (z[2] + 2) % 4)
        elif name == "Z":
            x = self.X[q]
            self.X[q] = (x[0], x[1], (x[2] + 2) % 4)
        else:
            raise ValueError(f"not a Clifford gate: {g}")


# --- Circuit A --------------------------------------------------------------------------

def make_rounds(n: int, rounds: int, rng: random.Random):
    """A's rounds: (the CX layer, the single-qubit layer)."""
    out = []
    for _ in range(rounds):
        wires = list(range(n))
        rng.shuffle(wires)
        cxs = []
        for i in range(0, n - 1, 2):
            c, t = wires[i], wires[i + 1]
            if rng.random() < 0.5:
                c, t = t, c
            cxs.append(("CX", c, t))
        layer = []
        for q in range(n):
            u = rng.random()
            if u < 0.25:
                layer.append(("H", q))
            elif u < 0.5:
                layer.append(("S", q))
            elif u < 0.75:
                layer.append(("T" if rng.random() < 0.5 else "Tdg", q))
        out.append((cxs, layer))
    return out


# --- Circuit B --------------------------------------------------------------------------

def rotation_form(rounds_, n: int, nests: int, rng: random.Random):
    """A as `D · R_m ⋯ R_1`, nests inserted: the rotations `[x, z, k, tags]` in time
    order (`exp(-i k π/8 P)` for the Hermitian Pauli `P` of masks x, z), and the frame of
    D."""
    frame = Frame(n)
    sites = [(ri, q) for ri, (_, layer) in enumerate(rounds_) for g, q in layer
             if g in ("T", "Tdg")]
    hosts = set(rng.sample(sites, min(nests, len(sites)))) if n >= 4 else set()
    subsets = [S for size in range(1, 5) for S in itertools.combinations(range(4), size)]
    rots, t_index, nest_id = [], 0, 0
    for ri, (cxs, layer) in enumerate(rounds_):
        for g in cxs:
            frame.append(g)
        t_wires = [q for g, q in layer if g in ("T", "Tdg")]
        for g, q in layer:
            if g not in ("T", "Tdg"):
                frame.append((g, q))
                continue
            x, z, s = signed(frame.Z[q])
            rots.append([x, z, (s * (1 if g == "T" else -1)) % 16, [("t", t_index)]])
            t_index += 1
            if (ri, q) not in hosts:
                continue
            partners = [w for w in t_wires if w != q]
            rng.shuffle(partners)
            pool = [w for w in range(n) if w != q and w not in partners]
            rng.shuffle(pool)
            wires = [q] + (partners + pool)[:3]
            images = [frame.Z[w] for w in wires]
            order = list(subsets)
            rng.shuffle(order)
            for S in order:
                p = (0, 0, 0)
                for i in S:
                    p = pmul(p, images[i])
                x, z, s = signed(p)
                eps = 1 if len(S) % 2 else -1
                rots.append([x, z, (s * eps) % 16,
                             [("nest", nest_id, tuple(wires[i] for i in S))]])
            nest_id += 1
    return rots, frame, nest_id


def merge(rots, window: int = 400):
    """Merge rotations about equal Paulis through commuting neighbours."""
    out, merges = [], 0
    for rot in rots:
        i, placed = len(out) - 1, False
        while i >= 0 and len(out) - 1 - i < window:
            o = out[i]
            if o[0] == rot[0] and o[1] == rot[1]:
                o[2] = (o[2] + rot[2]) % 16
                o[3] = o[3] + rot[3]
                merges += 1
                if o[2] % 8 == 0:           # identity, or -I: a global phase
                    del out[i]
                placed = True
                break
            if not commute(o, rot):
                break
            i -= 1
        if not placed:
            out.append([rot[0], rot[1], rot[2], list(rot[3])])
    return out, merges


def shuffle(rots, rng: random.Random, passes: int):
    """Swap adjacent commuting rotations at random."""
    for _ in range(passes):
        order = list(range(len(rots) - 1))
        rng.shuffle(order)
        for i in order:
            if rng.random() < 0.5 and commute(rots[i], rots[i + 1]):
                rots[i], rots[i + 1] = rots[i + 1], rots[i]


def synth_rotation(x: int, z: int, k: int, rng: random.Random):
    """exp(-i k π/8 P), P the Hermitian Pauli of masks x, z, as gates up to global phase:
    basis change V, ladder L into a target wire, diag(1, ω^k'), L†, V†."""
    support = list(bits(x | z))
    V = []
    for j in support:
        a, b = (x >> j) & 1, (z >> j) & 1
        if a and not b:
            V.append(("H", j))
        elif a and b:
            V += [("Sdg", j), ("H", j)]
    p = (x, z, (x & z).bit_count() % 4)
    for g in V:
        p = conj(g, p)
    assert p[0] == 0 and p[1] == x | z and p[2] in (0, 2), p
    kk = k % 16 if p[2] == 0 else (-k) % 16
    t = rng.choice(support)
    others = [j for j in support if j != t]
    rng.shuffle(others)
    if rng.random() < 0.5:
        ladder = [("CX", j, t) for j in others]
    else:
        chain = others + [t]
        ladder = [("CX", chain[i], chain[i + 1]) for i in range(len(chain) - 1)]
    body = [(g, t) for g in PHASES[kk % 8]]
    return V + ladder + body + ladder[::-1] + [(INVERSE[g], q) for g, q in reversed(V)]


def synth_clifford(frame: Frame, n: int):
    """D's circuit from its frame, by elimination: find g_1 … g_r with
    g_r ⋯ g_1 · D† = I (the frame is D†'s tableau), so D = g_r ⋯ g_1."""
    X, Z, gates = list(frame.X), list(frame.Z), []

    def apply(g):
        for L in (X, Z):
            for i in range(n):
                L[i] = conj(g, L[i])
        gates.append(g)

    for k in range(n):
        above = ~((1 << k) - 1)
        if X[k][0] & above == 0:
            apply(("H", next(bits(X[k][1] & above))))
        if not (X[k][0] >> k) & 1:
            apply(("CX", next(bits(X[k][0] & above)), k))
        for m in list(bits(X[k][0] & above & ~(1 << k))):
            apply(("CX", k, m))
        rest = list(bits(X[k][1] & above & ~(1 << k)))
        if rest:
            if not (X[k][1] >> k) & 1:
                apply(("S", k))
            for m in rest:
                apply(("CX", m, k))
        if (X[k][1] >> k) & 1:
            apply(("Sdg", k))                   # Y → X
        for m in list(bits((Z[k][0] | Z[k][1]) & above & ~(1 << k))):
            a, b = (Z[k][0] >> m) & 1, (Z[k][1] >> m) & 1
            if a and b:
                apply(("S", m))
                apply(("H", m))
            elif a:
                apply(("H", m))
        for m in list(bits(Z[k][1] & above & ~(1 << k))):
            apply(("CX", m, k))
        if (Z[k][0] >> k) & 1:                  # Y → Z, X fixed
            apply(("H", k))
            apply(("S", k))
            apply(("H", k))
    for k in range(n):
        if X[k][2] == 2:
            apply(("Z", k))
        if Z[k][2] == 2:
            apply(("X", k))
    assert all(X[k] == (1 << k, 0, 0) and Z[k] == (0, 1 << k, 0) for k in range(n))
    return gates


def cancel(gates):
    """Remove adjacent inverse pairs, cascading."""
    out, stacks = [], defaultdict(list)
    for g in gates:
        wires = g[1:]
        tops = {stacks[w][-1] if stacks[w] else None for w in wires}
        if len(tops) == 1:
            i = tops.pop()
            if i is not None:
                h = out[i]
                inverse = (h == g) if g[0] == "CX" else (
                    h[0] != "CX" and h[1] == g[1] and h[0] == INVERSE[g[0]])
                if inverse:
                    out[i] = None
                    for w in wires:
                        stacks[w].pop()
                    continue
        out.append(g)
        for w in wires:
            stacks[w].append(len(out) - 1)
    return [g for g in out if g is not None]


def build(n: int, rounds: int, nests: int, seed: int, shuffle_passes: int = 3):
    """Circuits A, B, B- and the construction record."""
    rng = random.Random(seed)
    rounds_ = make_rounds(n, rounds, rng)
    a = [g for cxs, layer in rounds_ for g in cxs + layer]
    rots, frame, n_nests = rotation_form(rounds_, n, nests, rng)
    n_pushed = len(rots)
    rots, merges1 = merge(rots)
    shuffle(rots, rng, shuffle_passes)
    rots, merges2 = merge(rots)
    # Negating a rotation of odd k changes the product by exp(i k π/4 P), never a phase.
    # B-: an unmerged nest rotation of weight at least two in the nest's basis, with X or
    # Y on some wire, from the second half of B (tiny registers merge nests away, hence
    # the fallbacks). B-diag: a diagonal one with only diagonal rotations before it, so
    # the difference is a diagonal phase that no computational-basis stimulus can see.
    def pick(*preds):
        for pred in preds:
            i = next((i for i, r in enumerate(rots) if r[2] % 2 and pred(i, r)), None)
            if i is not None:
                return i
        return None

    def pure(r):
        return len(r[3]) == 1 and r[3][0][0] == "nest" and len(r[3][0][2]) >= 2

    flip = pick(lambda i, r: i >= len(rots) // 2 and pure(r) and r[0],
                lambda i, r: pure(r) and r[0], lambda i, r: r[0], lambda i, r: True)
    diag_prefix = len(rots)
    for i, r in enumerate(rots):
        if r[0]:
            diag_prefix = i
            break
    diag = pick(lambda i, r: i < diag_prefix and pure(r), lambda i, r: i < diag_prefix)
    clifford = synth_clifford(frame, n)

    def emit(rotations, synth_seed):
        srng = random.Random(synth_seed)
        body = []
        for x, z, k, _ in rotations:
            body += synth_rotation(x, z, k, srng)
        return cancel(body + clifford)

    def negated(i):
        if i is None:
            return None
        neg = [list(r) for r in rots]
        neg[i][2] = (-neg[i][2]) % 16
        return emit(neg, seed + 1)

    b = emit(rots, seed + 1)
    bneg, bdiag = negated(flip), negated(diag)

    def described(i):
        if i is None:
            return None
        r = rots[i]
        return {"index": i, "weight": (r[0] | r[1]).bit_count(), "diagonal": not r[0],
                "from": [list(t) for t in r[3]]}

    record = {
        "n": n, "rounds": rounds, "nests": n_nests, "seed": seed,
        "pushed_rotations": n_pushed, "rotations": len(rots), "merges": merges1 + merges2,
        "negated": described(flip), "negated_diagonal": described(diag),
        "rotation_weights": summary([(r[0] | r[1]).bit_count() for r in rots]),
    }
    return a, b, bneg, bdiag, rots, record


def summary(values):
    """Mean, median and maximum of a list of numbers."""
    if not values:
        return {}
    s = sorted(values)
    return {"mean": round(sum(s) / len(s), 1), "median": s[len(s) // 2], "max": s[-1]}


def stats(gates, n: int):
    """Gate counts and depth."""
    c = defaultdict(int)
    level = [0] * n
    for g in gates:
        c[g[0]] += 1
        d = max(level[w] for w in g[1:]) + 1
        for w in g[1:]:
            level[w] = d
    return {"gates": len(gates), "cx": c["CX"], "h": c["H"], "s": c["S"] + c["Sdg"],
            "t": c["T"] + c["Tdg"], "xz": c["X"] + c["Z"], "depth": max(level, default=0)}


def to_qasm(gates, n: int, comment: str) -> str:
    lines = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"// {comment}", f"qreg q[{n}];"]
    for g in gates:
        if g[0] == "CX":
            lines.append(f"cx q[{g[1]}],q[{g[2]}];")
        else:
            lines.append(f"{TO_QASM[g[0]]} q[{g[1]}];")
    return "\n".join(lines) + "\n"


def parse_qasm(text: str):
    """(n, gates) of a file written by `to_qasm`."""
    n, gates = None, []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith(("//", "OPENQASM", "include")):
            continue
        if line.startswith("qreg"):
            n = int(line.split("[")[1].split("]")[0])
            continue
        name, args = line.rstrip(";").split(None, 1)
        wires = [int(a.split("[")[1].rstrip("]")) for a in args.split(",")]
        gates.append(("CX" if name == "cx" else FROM_QASM[name], *wires))
    return n, gates


def make(n: int, rounds: int, nests: int, seed: int, out: Path) -> dict:
    """Write a.qasm, b.qasm, bneg.qasm, bdiag.qasm, rotations.json and meta.json under
    `out`."""
    t0 = time.time()
    a, b, bneg, bdiag, rots, record = build(n, rounds, nests, seed)
    out.mkdir(parents=True, exist_ok=True)
    tag = f"hard_pair n={n} rounds={rounds} nests={nests} seed={seed}"
    (out / "a.qasm").write_text(to_qasm(a, n, tag + ": A (random rounds)"))
    (out / "b.qasm").write_text(to_qasm(b, n, tag + ": B (Pauli-rotation form, nests)"))
    if bneg is not None:
        (out / "bneg.qasm").write_text(
            to_qasm(bneg, n, tag + ": B- (one dense nest rotation negated)"))
    if bdiag is not None:
        (out / "bdiag.qasm").write_text(
            to_qasm(bdiag, n, tag + ": B-diag (one diagonal rotation negated)"))
    (out / "rotations.json").write_text(json.dumps(
        [{"x": hex(x), "z": hex(z), "k": k, "from": [list(t) for t in tags]}
         for x, z, k, tags in rots]))
    record["sha256"] = {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                        for f in sorted(out.glob("*.qasm"))}
    record |= {"a": stats(a, n), "b": stats(b, n),
               "bneg": stats(bneg, n) if bneg else None,
               "bdiag": stats(bdiag, n) if bdiag else None,
               "seconds": round(time.time() - t0, 2)}
    (out / "meta.json").write_text(json.dumps(record, indent=1) + "\n")
    return record


# --- Dense simulation (numpy) -----------------------------------------------------------

def simulate(gates, state):
    """Apply gates to an array whose first axes are the wires (wire 0 first)."""
    import numpy as np
    r, w = 1 / math.sqrt(2), complex(math.cos(math.pi / 4), math.sin(math.pi / 4))
    mult = {"Z": -1, "S": 1j, "Sdg": -1j, "T": w, "Tdg": w.conjugate()}
    nd = state.ndim
    for g in gates:
        if g[0] == "CX":
            c, t = g[1], g[2]
            i = [slice(None)] * nd
            i[c] = 1
            sub = state[tuple(i)]
            tt = t if t < c else t - 1
            j0, j1 = [slice(None)] * sub.ndim, [slice(None)] * sub.ndim
            j0[tt], j1[tt] = 0, 1
            tmp = sub[tuple(j0)].copy()
            sub[tuple(j0)] = sub[tuple(j1)]
            sub[tuple(j1)] = tmp
            continue
        name, q = g
        i0, i1 = [slice(None)] * nd, [slice(None)] * nd
        i0[q], i1[q] = 0, 1
        i0, i1 = tuple(i0), tuple(i1)
        if name == "H":
            a0 = state[i0].copy()
            state[i0] = (a0 + state[i1]) * r
            state[i1] = (a0 - state[i1]) * r
        elif name == "X":
            tmp = state[i0].copy()
            state[i0] = state[i1]
            state[i1] = tmp
        else:
            state[i1] *= mult[name]
    return state


def unitary(gates, n: int):
    import numpy as np
    u = np.eye(2 ** n, dtype=complex).reshape((2,) * n + (2 ** n,))
    return simulate(gates, u).reshape(2 ** n, 2 ** n)


def same_up_to_phase(u, v, tol: float = 1e-7) -> bool:
    import numpy as np
    i = np.unravel_index(np.argmax(np.abs(u)), u.shape)
    ph = v[i] / u[i]
    return abs(abs(ph) - 1) < tol and float(np.max(np.abs(v - ph * u))) < tol


def pauli_matrix(p, n: int):
    import numpy as np
    x, z, r = p
    I2, X2, Z2 = np.eye(2), np.array([[0, 1], [1, 0]]), np.diag([1, -1])
    m = np.eye(1)
    for j in range(n):
        f = (X2 if (x >> j) & 1 else I2) @ (Z2 if (z >> j) & 1 else I2)
        m = np.kron(m, f)
    return (1j ** r) * m


def self_test() -> int:
    import numpy as np
    rng = random.Random(0)
    n = 3
    # Pauli products and conjugations against matrices.
    for _ in range(200):
        a = (rng.randrange(8), rng.randrange(8), rng.randrange(4))
        b = (rng.randrange(8), rng.randrange(8), rng.randrange(4))
        assert np.allclose(pauli_matrix(pmul(a, b), n), pauli_matrix(a, n) @ pauli_matrix(b, n))
        for g in [("H", 1), ("S", 0), ("Sdg", 2), ("X", 1), ("Z", 0), ("CX", 0, 2), ("CX", 2, 1)]:
            G = unitary([g], n)
            assert np.allclose(pauli_matrix(conj(g, a), n), G @ pauli_matrix(a, n) @ G.conj().T), g
    # The frame: Φ(P) = D† P D for random Clifford circuits.
    for _ in range(20):
        gs = [rng.choice([("H", rng.randrange(n)), ("S", rng.randrange(n)),
                          ("Sdg", rng.randrange(n)), ("X", rng.randrange(n)),
                          ("Z", rng.randrange(n)), ("CX",) + tuple(rng.sample(range(n), 2))])
              for _ in range(15)]
        f = Frame(n)
        for g in gs:
            f.append(g)
        D = unitary(gs, n)
        for q in range(n):
            for img, P in ((f.X[q], (1 << q, 0, 0)), (f.Z[q], (0, 1 << q, 0))):
                assert np.allclose(pauli_matrix(img, n), D.conj().T @ pauli_matrix(P, n) @ D)
        # Clifford synthesis from the frame.
        assert same_up_to_phase(unitary(synth_clifford(f, n), n), D)
    # Rotation synthesis.
    for _ in range(100):
        nn = 4
        x, z = rng.randrange(1, 16), rng.randrange(16)
        k = rng.randrange(1, 16)
        P = pauli_matrix((x, z, (x & z).bit_count() % 4), nn)
        th = k * math.pi / 8
        R = math.cos(th) * np.eye(2 ** nn) - 1j * math.sin(th) * P
        assert same_up_to_phase(unitary(synth_rotation(x, z, k, rng), nn), R)
    # A spider nest multiplies to a global phase.
    nn = 5
    f = Frame(nn)
    for g in [("H", 0), ("CX", 0, 1), ("S", 2), ("H", 3), ("CX", 3, 4), ("CX", 1, 3)]:
        f.append(g)
    imgs = [f.Z[w] for w in (0, 2, 3, 4)]
    N = np.eye(2 ** nn)
    for size in range(1, 5):
        for S in itertools.combinations(range(4), size):
            p = (0, 0, 0)
            for i in S:
                p = pmul(p, imgs[i])
            x, z, s = signed(p)
            eps = 1 if size % 2 else -1
            th = s * eps * math.pi / 8
            N = N @ (math.cos(th) * np.eye(2 ** nn)
                     - 1j * math.sin(th) * pauli_matrix((x, z, (x & z).bit_count() % 4), nn))
    assert same_up_to_phase(N, np.eye(2 ** nn))
    # End to end: A ≡ B, A ≢ B-.
    for n_, rounds, nests, seed in [(4, 6, 2, 1), (5, 8, 3, 2), (6, 8, 4, 3), (7, 10, 5, 4),
                                    (6, 12, 6, 5)]:
        a, b, bneg, bdiag, _, rec = build(n_, rounds, nests, seed)
        UA, UB = unitary(a, n_), unitary(b, n_)
        assert same_up_to_phase(UA, UB), (n_, seed)
        assert bneg is not None and not same_up_to_phase(UA, unitary(bneg, n_)), (n_, seed)
        diff = sum(1 for g, h in zip(b, bneg) if g != h) + abs(len(b) - len(bneg))
        line = (f"n={n_}: A {len(a)} gates, B {len(b)} gates, {rec['rotations']} rotations, "
                f"{rec['merges']} merges; A ≡ B, A ≢ B- (differs from B in {diff} gate(s))")
        if bdiag is not None:
            M = UA.conj().T @ unitary(bdiag, n_)
            off = M - np.diag(np.diag(M))
            assert float(np.max(np.abs(off))) < 1e-7, "B-diag's difference is not diagonal"
            assert not same_up_to_phase(M, np.eye(2 ** n_)), (n_, seed)
            line += ", A ≢ B-diag, their difference diagonal"
        print(line)
    # QASM round trip, and PyZX as an independent reader.
    a, b, _, _, _, _ = build(5, 8, 3, 7)
    for gs in (a, b):
        assert parse_qasm(to_qasm(gs, 5, "t"))[1] == gs
    try:
        import pyzx as zx
    except ImportError:
        print("pyzx not importable: independent QASM reader skipped")
    else:
        ta = np.asarray(zx.Circuit.from_qasm(to_qasm(a, 5, "t")).to_matrix())
        tb = np.asarray(zx.Circuit.from_qasm(to_qasm(b, 5, "t")).to_matrix())
        assert same_up_to_phase(ta, tb)
        flipped = [(g[0],) + tuple(4 - w for w in g[1:]) for g in a]
        assert same_up_to_phase(ta, unitary(a, 5)) or same_up_to_phase(ta, unitary(flipped, 5))
        print("PyZX reads A and B as the same unitary, and A as ours")
    print("self-test passed")
    return 0


# --- Checkers (one per child process) ---------------------------------------------------

def check(name: str, a: Path, b: Path, timeout: float) -> dict:
    """Run one checker on (a, b); return {verdict, ...}."""
    t0 = time.time()
    if name == "dense":
        n, ga = parse_qasm(a.read_text())
        _, gb = parse_qasm(b.read_text())
        ok = same_up_to_phase(unitary(ga, n), unitary(gb, n))
        return {"verdict": "equivalent" if ok else "not_equivalent"}
    if name == "stimuli":
        import numpy as np
        n, ga = parse_qasm(a.read_text())
        _, gb = parse_qasm(b.read_text())
        rng = np.random.default_rng(0)
        r = 1 / math.sqrt(2)
        states = [np.array([1, 0]), np.array([0, 1]), np.array([r, r]), np.array([r, -r]),
                  np.array([r, 1j * r]), np.array([r, -1j * r])]
        done, per = 0, None
        while done < 16:
            if per is not None and time.time() - t0 + per > 0.9 * timeout:
                break
            s0 = time.time()
            psi = np.array([1.0 + 0j])
            for _ in range(n):
                psi = np.kron(psi, states[rng.integers(6)])
            psi = psi.reshape((2,) * n)
            fa = simulate(ga, psi.copy()).reshape(-1)
            fb = simulate(gb, psi).reshape(-1)
            fid = abs(np.vdot(fa, fb)) ** 2
            done += 1
            per = time.time() - s0
            if fid < 1 - 1e-8:
                return {"verdict": "not_equivalent", "stimuli": done}
        if done == 0:
            return {"verdict": "timeout", "stimuli": 0}
        return {"verdict": "probably_equivalent", "stimuli": done}
    if name == "pyzx":
        import pyzx as zx
        ca, cb = zx.Circuit.load(str(a)), zx.Circuit.load(str(b))
        ok = ca.verify_equality(cb)
        return {"verdict": "equivalent" if ok else "inconclusive"}
    if name == "quizx":
        import quizx
        text_a, text_b = a.read_text(), b.read_text()
        body_b = [l for l in text_b.splitlines() if l and l.split()[0] in QASM_INVERSE]
        inv = [QASM_INVERSE[l.split()[0]] + l[len(l.split()[0]):] for l in reversed(body_b)]
        m = quizx.qasm(text_a + "\n".join(inv) + "\n")
        quizx.full_simp(m)
        ins, outs = list(m.inputs()), list(m.outputs())
        ident = m.num_vertices() == len(ins) + len(outs) and all(
            list(m.neighbors(v)) == [w] and m.edge_type(m.edge(v, w)) == 1
            for v, w in zip(ins, outs))
        nonclifford = sum(1 for v in m.vertices()
                          if (m.phase(v) * 4) % 2 != 0) if not ident else 0
        return {"verdict": "equivalent" if ident else "inconclusive",
                "residual_spiders": m.num_vertices() - len(ins) - len(outs),
                "residual_non_clifford": nonclifford}
    if name.startswith("qcec"):
        from mqt import qcec
        opts = {"timeout": float(timeout)}
        if name == "qcec_dd":
            opts |= {"run_alternating_checker": True, "run_simulation_checker": False,
                     "run_zx_checker": False}
        elif name == "qcec_zx":
            opts |= {"run_alternating_checker": False, "run_simulation_checker": False,
                     "run_zx_checker": True}
        elif name == "qcec_sim":
            opts |= {"run_alternating_checker": False, "run_simulation_checker": True,
                     "run_zx_checker": False}
        res = qcec.verify(str(a), str(b), **opts)
        return {"verdict": str(res.equivalence).split(".")[-1]}
    raise ValueError(f"unknown checker {name}")


def run_child(py: str, name: str, a: Path, b: Path, timeout: float, mem_gb: float) -> dict:
    """Run `check` in a child under a wall-clock timeout and a resident-memory watchdog.
    The child runs in the pair's directory on relative names: QCEC's loader reports some
    long absolute paths as missing."""
    assert a.parent == b.parent
    cmd = [py, str(Path(__file__).resolve()), "check", name, a.name, b.name,
           "--timeout", str(timeout)]
    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         cwd=a.parent)
    peak, status = 0, None
    while p.poll() is None:
        try:
            rss = int(subprocess.run(["ps", "-o", "rss=", "-p", str(p.pid)],
                                     capture_output=True, text=True).stdout.strip() or 0)
        except ValueError:
            rss = 0
        peak = max(peak, rss)
        if rss > mem_gb * 2 ** 20:
            status = "memout"
        elif time.time() - t0 > timeout + 30:
            status = "timeout"
        if status:
            p.kill()
            p.wait()
            break
        time.sleep(0.25)
    secs = round(time.time() - t0, 2)
    base = {"seconds": secs, "peak_gb": round(peak / 2 ** 20, 2)}
    if status:
        return base | {"verdict": status}
    out, err = p.communicate()
    try:
        return base | json.loads(out.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        return base | {"verdict": "error", "error": (err.strip().splitlines() or ["?"])[-1][:200]}


# A checker that ran out of time or memory at one rung is skipped above it; an error is
# recorded and the checker tried again at the next rung.
FAILED = {"timeout", "memout"}
# The checkers that can tell a diagonal difference from none: complete ones and simulation.
DIAG_CHECKERS = {"dense", "stimuli", "qcec", "qcec_dd", "qcec_sim"}


def ladder(args) -> int:
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    rungs = [int(v) for v in args.rungs.split(",")]
    checkers = args.checkers.split(",")
    results, broke = [], {}
    rpath = out / "results.json"
    for n in rungs:
        rounds, nests = n, max(1, math.ceil(5 * n / 8))
        d = out / f"n{n:03d}"
        rec = make(n, rounds, nests, args.seed, d)
        print(f"== n={n}: A {rec['a']['gates']} gates (T {rec['a']['t']}, H {rec['a']['h']}, "
              f"CX {rec['a']['cx']}, depth {rec['a']['depth']}); B {rec['b']['gates']} gates "
              f"(T {rec['b']['t']}, H {rec['b']['h']}, CX {rec['b']['cx']}); "
              f"{rec['rotations']} rotations, weight {rec['rotation_weights']}", flush=True)
        for name in checkers:
            for pair, fname in (("equiv", "b.qasm"), ("mutant", "bneg.qasm"),
                                ("diag_mutant", "bdiag.qasm")):
                if pair == "diag_mutant" and name not in DIAG_CHECKERS:
                    continue            # the ZX checkers are inconclusive on every pair
                if not (d / fname).exists():
                    continue
                row = {"n": n, "checker": name, "pair": pair}
                if name == "dense" and n > args.dense_max:
                    row |= {"verdict": "skipped", "why": f"n > {args.dense_max}"}
                elif (name, pair) in broke:
                    row |= {"verdict": "skipped", "why": f"failed at n={broke[(name, pair)]}"}
                else:
                    row |= run_child(sys.executable, name, d / "a.qasm", d / fname,
                                     args.timeout, args.mem_gb)
                    if row["verdict"] in FAILED:
                        broke[(name, pair)] = n
                results.append(row)
                rpath.write_text(json.dumps(results, indent=1) + "\n")
                extra = {k: v for k, v in row.items()
                         if k not in ("n", "checker", "pair", "verdict")}
                print(f"n={n} {name} {pair}: {row['verdict']} {extra}", flush=True)
    print("ladder done", flush=True)
    return 0


# What each verdict says about each pair: decided (✓), evidence only (≈), no answer (?),
# a wrong indication (✗), out of time or memory (T, M), not run (·).
def mark(pair: str, verdict: str) -> str:
    if verdict in ("timeout", "memout"):
        return verdict[0].upper()
    if verdict in ("skipped", "error"):
        return "·"
    equal = verdict in ("equivalent", "equivalent_up_to_global_phase")
    if pair == "equiv":
        return {True: "✓"}.get(equal) or {"probably_equivalent": "≈", "not_equivalent": "✗",
                                          "probably_not_equivalent": "✗"}.get(verdict, "?")
    if verdict == "not_equivalent":
        return "✓"
    if verdict == "probably_not_equivalent":
        return "≈"
    if equal or verdict == "probably_equivalent":
        return "✗"
    return "?"


def table(out: Path) -> str:
    """The ladder under `out` as Markdown: the pairs' sizes, then one row per checker."""
    rows = json.loads((out / "results.json").read_text())
    ns = sorted({r["n"] for r in rows})
    lines = ["| Qubits | Rounds | Nests | A: gates / CX / H / T / depth | B: gates / CX / H / T "
             "| Rotations (median weight) |", "|---:|---:|---:|---|---|---|"]
    for n in ns:
        m = json.loads((out / f"n{n:03d}" / "meta.json").read_text())
        a, b = m["a"], m["b"]
        lines.append(f"| {n} | {m['rounds']} | {m['nests']} | {a['gates']} / {a['cx']} / {a['h']} "
                     f"/ {a['t']} / {a['depth']} | {b['gates']} / {b['cx']} / {b['h']} / {b['t']} "
                     f"| {m['rotations']} ({m['rotation_weights'].get('median', '—')}) |")
    by = defaultdict(dict)
    for r in rows:
        by[r["checker"]][(r["n"], r["pair"])] = r
    lines += ["", "| Checker | " + " | ".join(f"n = {n}" for n in ns) + " |",
              "|---|" + "---|" * len(ns)]
    for name, cells in by.items():
        row = []
        for n in ns:
            marks = [mark(pair, cells[(n, pair)]["verdict"])
                     for pair in ("equiv", "mutant", "diag_mutant") if (n, pair) in cells]
            row.append(" ".join(marks) if marks else "·")
        lines.append(f"| `{name}` | " + " | ".join(row) + " |")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--self-test", action="store_true")
    sub = ap.add_subparsers(dest="cmd")
    m = sub.add_parser("make")
    m.add_argument("--n", type=int, required=True)
    m.add_argument("--rounds", type=int)
    m.add_argument("--nests", type=int)
    m.add_argument("--seed", type=int, default=1)
    m.add_argument("--out", required=True)
    c = sub.add_parser("check")
    c.add_argument("name")
    c.add_argument("a")
    c.add_argument("b")
    c.add_argument("--timeout", type=float, default=300)
    lad = sub.add_parser("ladder")
    lad.add_argument("--rungs", default="8,12,16,24,32,40,64")
    lad.add_argument("--checkers",
                     default="dense,stimuli,pyzx,quizx,qcec,qcec_dd,qcec_zx,qcec_sim")
    lad.add_argument("--timeout", type=float, default=300)
    lad.add_argument("--mem-gb", type=float, default=6)
    lad.add_argument("--dense-max", type=int, default=12)
    lad.add_argument("--seed", type=int, default=1)
    lad.add_argument("--out", default=str(HARNESS_HOME / "hard-pair"))
    tab = sub.add_parser("table", help="the ladder's results as Markdown")
    tab.add_argument("--out", default=str(HARNESS_HOME / "hard-pair"))
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    if args.cmd is None:
        ap.error("a subcommand or --self-test")
    if args.cmd == "make":
        rec = make(args.n, args.rounds or args.n, args.nests or max(1, math.ceil(5 * args.n / 8)),
                   args.seed, Path(args.out))
        print(json.dumps(rec, indent=1))
        return 0
    if args.cmd == "table":
        print(table(Path(args.out)), end="")
        return 0
    if args.cmd == "check":
        print(json.dumps(check(args.name, Path(args.a), Path(args.b), args.timeout)), flush=True)
        return 0
    return ladder(args)


if __name__ == "__main__":
    sys.exit(main())
