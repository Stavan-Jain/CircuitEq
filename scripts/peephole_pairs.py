#!/usr/bin/env python3
"""Seeded Clifford+T pairs for the agent harness: a random circuit and a peephole twin.

The harness needs pairs that appear nowhere in the repository, at sizes the
promoted benchmarks do not reach, without depending on an external optimiser.
This script makes them. The original is a seeded random circuit over the whole
alphabet (`H X Y Z S Sdg T Tdg` and `CX`). The twin is what a peephole pass
leaves: a gate is moved right through the gates it commutes with, by exactly the
rules of `Instr.CanCommute` (the Python mirror in `certificate.py`), until it
meets a partner it cancels against (`Instr.CanCancel`) or fuses with (two
diagonal gates on one wire whose phases add up to a single gate: `T T = S`,
`S S = Z`, `Z S = Sdg`, …). Every rewrite is an exact identity, so the pair is
equal as unitaries, and a proof inside the library's vocabulary exists: the
cancellations and the one-wire fusion windows, with checked commutations
between them. Finding it at a thousand gates is the task.

The twin keeps the skeleton (it only deletes gates and edits phases), which is
the shape of phase-folding output (TZAP, PyZX phase teleportation).

The script is untrusted, like every generator here: the Lean kernel judges the
pair. As a check on the generator itself, both circuits are applied to one
random state vector in floating point and compared.

Usage::

    python3 scripts/peephole_pairs.py --qubits 8 --gates 1000 --seed 1 --out pair.json
    python3 scripts/agent_harness.py import-pair pair.json

`--mutant K` deletes gate `K mod len` of the twin, which always breaks the
pair (no gate of the alphabet is a scalar).
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from certificate import DIAG, INVERSE, can_cancel, can_commute, cnot, fmt_instr, one  # noqa: E402

# Diagonal gates as multiples of pi/4, and back.
PHASE = {"T": 1, "S": 2, "Z": 4, "Sdg": 6, "Tdg": 7}
GATE_OF_PHASE = {v: k for k, v in PHASE.items()}

# How often each gate is drawn. CNOTs and Hadamards keep the circuit from being
# a product of one-wire circuits; the rest of the alphabet is all present.
WEIGHTS = {"CX": 30, "H": 14, "T": 14, "Tdg": 10, "S": 8, "Sdg": 6, "Z": 6, "X": 7, "Y": 5}


def random_circuit(qubits: int, gates: int, seed: int) -> list[tuple]:
    rng = random.Random(seed)
    names, weights = list(WEIGHTS), list(WEIGHTS.values())
    out = []
    for _ in range(gates):
        name = rng.choices(names, weights)[0]
        if name == "CX":
            c, t = rng.sample(range(qubits), 2)
            out.append(cnot(c, t))
        else:
            out.append(one(name, rng.randrange(qubits)))
    return out


def fuse(a: tuple, b: tuple) -> list[tuple] | None:
    """What `a` followed immediately by `b` rewrites to, if the pass knows: nothing for an
    inverse pair, one gate for two diagonal gates whose phases add up to a single gate."""
    if can_cancel(a, b):
        return []
    if a[0] == "one" and b[0] == "one" and a[2] == b[2] and a[1] in DIAG and b[1] in DIAG:
        total = (PHASE[a[1]] + PHASE[b[1]]) % 8
        if total == 0:
            return []
        if total in GATE_OF_PHASE:
            return [one(GATE_OF_PHASE[total], a[2])]
    return None


def peephole(circuit: list[tuple]) -> tuple[list[tuple], int]:
    """Repeat until nothing changes: move a gate right through what it commutes with and
    fuse it with the first partner it meets. The fused gate takes the partner's place, which
    is where the moved gate has provably arrived. Returns the twin and the rewrite count."""
    c, rewrites, changed = list(circuit), 0, True
    while changed:
        changed = False
        i = 0
        while i < len(c):
            j = i + 1
            while j < len(c):
                fused = fuse(c[i], c[j])
                if fused is not None:
                    c[j:j + 1] = fused
                    del c[i]
                    rewrites += 1
                    changed = True
                    i -= 1
                    break
                if not can_commute(c[i], c[j]):
                    break
                j += 1
            i += 1
    return c, rewrites


# A floating-point state-vector simulator, only to check the generator.
R = 1 / math.sqrt(2)
MATRICES = {
    "H": ((R, R), (R, -R)), "X": ((0, 1), (1, 0)), "Y": ((0, -1j), (1j, 0)),
    "Z": ((1, 0), (0, -1)), "S": ((1, 0), (0, 1j)), "Sdg": ((1, 0), (0, -1j)),
    "T": ((1, 0), (0, cmath.exp(1j * math.pi / 4))),
    "Tdg": ((1, 0), (0, cmath.exp(-1j * math.pi / 4))),
}


def apply(circuit: list[tuple], psi: list[complex]) -> list[complex]:
    for g in circuit:
        new = list(psi)
        if g[0] == "one":
            m, bit = MATRICES[g[1]], 1 << g[2]
            for x in range(len(psi)):
                b = 1 if x & bit else 0
                new[x] = m[b][b] * psi[x] + m[b][1 - b] * psi[x ^ bit]
        else:
            cbit, tbit = 1 << g[1], 1 << g[2]
            for x in range(len(psi)):
                if x & cbit:
                    new[x] = psi[x ^ tbit]
        psi = new
    return psi


def distance(a: list[tuple], b: list[tuple], qubits: int, seed: int) -> float:
    """The largest amplitude difference of the two circuits on one random state."""
    rng = random.Random(seed)
    psi = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(2 ** qubits)]
    return max(abs(x - y) for x, y in zip(apply(a, psi), apply(b, psi)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--qubits", type=int, required=True)
    parser.add_argument("--gates", type=int, required=True)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--mutant", type=int, help="delete this gate (mod length) of the twin")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    original = random_circuit(args.qubits, args.gates, args.seed)
    twin, rewrites = peephole(original)
    name = f"peephole_{args.qubits}q_{args.gates}g_s{args.seed}"
    expected = "equiv"
    if args.mutant is not None:
        k = args.mutant % len(twin)
        del twin[k]
        name, expected = f"{name}_mut{args.mutant}", "not_equiv"
    gap = distance(original, twin, args.qubits, args.seed)
    if (gap < 1e-9) != (expected == "equiv"):
        raise SystemExit(f"the generator is wrong: distance {gap:.3g} but expected {expected}")
    used = sorted({g[1] if g[0] == "one" else "CX" for g in original})
    tcount = [sum(g[0] == "one" and g[1] in ("T", "Tdg") for g in c) for c in (original, twin)]
    pair = {
        "name": name, "qubits": args.qubits, "relation": "u", "expected": expected,
        "split": "held-out", "family": "peephole", "rung": args.gates,
        "original": [fmt_instr(g) for g in original], "optimized": [fmt_instr(g) for g in twin],
        "source": {"generator": "scripts/peephole_pairs.py", "seed": args.seed,
                   "rewrites": rewrites, "tcount": tcount, "alphabet": used,
                   "float_distance_on_a_random_state": gap},
        # The generator says how the twin was made; an agent under test does not get it.
        "holdout_delete": ["scripts/peephole_pairs.py"],
    }
    args.out.write_text(json.dumps(pair, indent=1) + "\n")
    print(f"{name}: {len(original)} -> {len(twin)} gates, {rewrites} rewrites, "
          f"T-count {tcount[0]} -> {tcount[1]}, alphabet {used}, distance {gap:.2g}")


if __name__ == "__main__":
    main()
