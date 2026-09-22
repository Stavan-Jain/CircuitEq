"""Scale test: the fragment checkers on larger circuits.

Generates seeded circuits of increasing size, optimises them with PyZX, and
asks the kernel to certify each pair with the checker for its fragment,
measuring wall time and peak memory of the Lean process.

Families (``--family``), with the default pipeline and the checker:

* ``clifford``: random ``H``, ``S``, ``CX`` on ``n`` qubits; ``full_reduce``
  (a re-synthesis); ``tableauChecker n`` (``≡ₛ``).
* ``ghz``: the GHZ ladder ``H 0; CX 0 1; …; CX (n-2) (n-1)``; ``full_reduce``;
  tableau.
* ``surface``: ``--rounds`` rounds of syndrome extraction of the rotated
  surface code of distance ``d`` (the size argument), unitary part only, on
  ``2 d² − 1`` qubits; ``full_reduce``; tableau.
* ``cnot_t``: random ``CX`` and ``T`` on ``n`` qubits; ``teleport`` (phase
  folding); ``phasePolyChecker n`` (``≡ᵤ``).
* ``ccz_net``: ``2 n`` CCZ gadgets (``CX`` and ``T``, no Hadamard, every
  parity of weight at most three) on random triples of ``n`` wires;
  ``teleport``; phase polynomial.

Pipelines (``--pipeline``): ``full_reduce`` and ``teleport`` as in
``check_pyzx_benchmarks.py``, and ``basic``, PyZX's peephole
``basic_optimization`` alone, which keeps the size linear.

For every pair a *mutant* (one gate of the optimised circuit deleted) is
also checked: the phase polynomial refutes it (``phasePolyRefutes_sound``),
the tableau rejects it. With ``--chunk G`` the tableau check is emitted as
one theorem per ``G`` generators (``CircuitEq/Chunk.lean``), so the kernel's
memory is bounded by one chunk; a Python mirror of the Pauli update rules
pre-checks the pair and names the generator that witnesses the mutant.

Two Lean files are produced per size, one with only the definitions
(elaboration cost) and one with the theorems, so the kernel's share is the
difference. Requires pyzx==0.9.0. Results go to a JSON file; ``--table``
prints them as Markdown.
"""

import argparse
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_pyzx_benchmarks as cpb  # noqa: E402
from chunks import CHUNK_HEADER, chunk_theorems, run_lean  # noqa: E402

import pyzx as zx  # noqa: E402
from pyzx.circuit.gates import CNOT, HAD, S, T, ZPhase  # noqa: E402
from fractions import Fraction  # noqa: E402

TABLEAU_FAMILIES = {"clifford", "ghz", "surface"}
DEFAULT_PIPELINE = {"clifford": "full_reduce", "ghz": "full_reduce", "surface": "full_reduce",
                    "cnot_t": "teleport", "ccz_net": "teleport"}
CLIFFORD_GATES = {"H", "X", "Y", "Z", "S", "Sdg", "CX"}
PHASE_POLY_GATES = {"CX", "Z", "S", "Sdg", "T", "Tdg"}


def surface_stabilizers(d: int) -> list[tuple[str, list[int]]]:
    """The ``d² − 1`` stabilizers of the rotated surface code: type and data qubits."""
    out = []
    for r in range(-1, d):
        for c in range(-1, d):
            qs = [(r + dr) * d + (c + dc) for dr in (0, 1) for dc in (0, 1)
                  if 0 <= r + dr < d and 0 <= c + dc < d]
            kind = "X" if (r + c) % 2 == 0 else "Z"
            boundary = (kind == "X" and r in (-1, d - 1)) or (kind == "Z" and c in (-1, d - 1))
            if len(qs) == 4 or (len(qs) == 2 and boundary):
                out.append((kind, qs))
    assert len(out) == d * d - 1
    return out


def make_circuit(family: str, size: int, gates: int, seed: int, rounds: int) -> zx.Circuit:
    """The seeded circuit of the family; ``size`` is qubits, or the distance for ``surface``."""
    rng = random.Random(seed)
    if family == "ghz":
        c = zx.Circuit(size)
        c.gates.append(HAD(0))
        c.gates += [CNOT(i, i + 1) for i in range(size - 1)]
        return c
    if family == "surface":
        stabs = surface_stabilizers(size)
        c = zx.Circuit(2 * size * size - 1)
        for _ in range(rounds):
            for k, (kind, qs) in enumerate(stabs):
                a = size * size + k
                if kind == "X":
                    c.gates.append(HAD(a))
                    c.gates += [CNOT(a, q) for q in qs]
                    c.gates.append(HAD(a))
                else:
                    c.gates += [CNOT(q, a) for q in qs]
        return c
    c = zx.Circuit(size)
    if family == "ccz_net":
        tdg = Fraction(7, 4)
        for _ in range(2 * size):
            x, y, z = rng.sample(range(size), 3)
            c.gates += [T(x), T(y), T(z)]
            for u, v in ((x, y), (x, z), (y, z)):
                c.gates += [CNOT(u, v), ZPhase(v, tdg), CNOT(u, v)]
            c.gates += [CNOT(x, z), CNOT(y, z), T(z), CNOT(y, z), CNOT(x, z)]
        return c
    for _ in range(gates):
        kind = rng.choice(["H", "S", "CX", "CX"] if family == "clifford" else ["T", "CX", "CX"])
        if kind == "CX":
            a, b = rng.sample(range(size), 2)
            c.gates.append(CNOT(a, b))
        elif kind == "H":
            c.gates.append(HAD(rng.randrange(size)))
        elif kind == "S":
            c.gates.append(S(rng.randrange(size)))
        else:
            c.gates.append(T(rng.randrange(size)))
    return c


def optimize(circuit: zx.Circuit, pipeline: str) -> zx.Circuit:
    """Run a PyZX pipeline; ``basic`` is the peephole pass alone."""
    if pipeline == "basic":
        return zx.optimize.basic_optimization(circuit.to_basic_gates())
    return cpb.optimize(circuit, pipeline)


def in_fragment(instrs: list[str], family: str) -> bool:
    """Whether every instruction is in the checker's fragment."""
    allowed = CLIFFORD_GATES if family in TABLEAU_FAMILIES else PHASE_POLY_GATES
    return all(ins.split()[0] in allowed for ins in instrs)


# A Python mirror of `Pauli.conj*` in `CircuitEq/Tableau.lean`: `(x, z, phase)`
# denotes `i^phase · Z^z · X^x`. Nothing here is trusted; it pre-checks a pair
# and finds the generator on which a mutant differs.

def conj(instrs: list[str], pauli: tuple[int, int, int]) -> tuple[int, int, int]:
    """Conjugate a Pauli string through a Clifford circuit."""
    x, z, p = pauli
    for ins in instrs:
        parts = ins.split()
        if parts[0] == "CX":
            c, t = int(parts[1]), int(parts[2])
            xc, zt = x >> c & 1, z >> t & 1
            x ^= xc << t
            z ^= zt << c
            continue
        j = int(parts[1])
        xb, zb = x >> j & 1, z >> j & 1
        if parts[0] == "H":
            if xb ^ zb:
                x ^= 1 << j
                z ^= 1 << j
            p += 2 * (xb & zb)
        elif parts[0] == "S":
            z ^= xb << j
            p += 3 * xb
        elif parts[0] == "Sdg":
            z ^= xb << j
            p += xb
        elif parts[0] == "X":
            p += 2 * zb
        elif parts[0] == "Z":
            p += 2 * xb
        elif parts[0] == "Y":
            p += 2 * (xb ^ zb)
        else:
            raise ValueError(f"not Clifford: {ins}")
    return x, z, p % 4


def gen_at(n: int, g: int) -> tuple[int, int, int]:
    """`Tableau.genAt n g`: `X_g` below `n`, `Z_{g-n}` from `n` on."""
    return (1 << g, 0, 0) if g < n else (0, 1 << (g - n), 0)


def first_difference(n: int, a: list[str], b: list[str]) -> int | None:
    """The first generator whose images under the two circuits differ."""
    for g in range(2 * n):
        if conj(a, gen_at(n, g)) != conj(b, gen_at(n, g)):
            return g
    return None


def lean_list(instrs: list[str]) -> str:
    """Format instructions as a Lean list literal, eight per line."""
    rows = [", ".join(instrs[i:i + 8]) for i in range(0, len(instrs), 8)]
    return "[" + ",\n    ".join(rows) + "]"


def lean_def(name: str, n: int, instrs: list[str]) -> str:
    """A circuit definition; long literals need a deeper recursion limit to compile."""
    prefix = "set_option maxRecDepth 1000000 in\n" if len(instrs) > 1000 else ""
    return f"{prefix}def {name} : Circuit {n} :=\n  {lean_list(instrs)}"


def lean_source(family: str, n: int, orig: list[str], opt: list[str], mut: list[str],
                theorems: bool, chunk: int, witness: int | None) -> str:
    """The Lean file for one pair."""
    tableau = family in TABLEAU_FAMILIES
    module = "CircuitEq.Tableau" if tableau else "CircuitEq.PhasePoly"
    out = [f"import {module}", "open Quantum Quantum.Circuit Instr", "",
           lean_def("original", n, orig), "", lean_def("optimized", n, opt), "",
           lean_def("mutant", n, mut), ""]
    if not theorems:
        return "\n".join(out)
    if not tableau:
        out += ["theorem equiv : original ≡ᵤ optimized :=",
                f"  (phasePolyChecker {n}).sound _ _ (by decide +kernel)", "",
                # complete on its fragment, so a mutant is refuted, not merely undecided
                "theorem mutant_refuted : ¬ (original ≡ᵤ mutant) :=",
                "  phasePolyRefutes_sound (by decide +kernel)", ""]
    elif chunk == 0:
        out += ["theorem equiv : original ≡ₛ optimized :=",
                f"  (tableauChecker {n}).sound _ _ (by decide +kernel)", "",
                f"theorem mutant_rejected : (tableauChecker {n}).check original mutant = false "
                ":= by", "  decide +kernel", ""]
    else:
        lines, term = chunk_theorems("tableauCheckGen original optimized", 2 * n, chunk, "g")
        out += [CHUNK_HEADER, ""] + lines
        out += ["theorem equiv : original ≡ₛ optimized :=",
                f"  tableau_sound_of_allBelow ({term})", ""]
        if witness is not None:
            out += [f"theorem mutant_rejected : tableauCheckGen original mutant {witness} = false "
                    ":= by", "  decide +kernel", ""]
    return "\n".join(out)


def run_size(args, size: int) -> dict:
    """Generate, optimise, emit and (optionally) check one size."""
    family = args.family
    pipeline = args.pipeline or DEFAULT_PIPELINE[family]
    original = make_circuit(family, size, args.gates_per_qubit * size, args.seed, args.rounds)
    n = original.qubits
    optimized = optimize(original, pipeline)
    orig, opt = cpb.lean_instructions(original), cpb.lean_instructions(optimized)
    rng = random.Random(args.seed + 1)
    # the mutant deletes one optimised gate; an empty optimised circuit (the pair is an
    # identity, as two rounds of surface-code extraction are) loses an original gate
    base = opt if opt else orig
    idx = rng.randrange(len(base))
    mut = base[:idx] + base[idx + 1:]
    rec = {"family": family, "pipeline": pipeline, "chunk": args.chunk, "qubits": n,
           "gates": len(orig), "opt_gates": len(opt), "tcount": original.tcount(),
           "opt_tcount": optimized.tcount(), "in_fragment": in_fragment(opt, family),
           "deleted": base[idx], "seed": args.seed}
    if family == "surface":
        rec["rounds"] = args.rounds
    witness = None
    if family in TABLEAU_FAMILIES and rec["in_fragment"]:
        rec["mirror_agrees"] = first_difference(n, orig, opt) is None
        witness = first_difference(n, orig, mut)
        rec["mutant_witness"] = witness
    args.workdir.mkdir(parents=True, exist_ok=True)
    stem = f"{family}_{pipeline}_n{n}_g{len(orig)}_s{args.seed}_c{args.chunk}"
    defs, full = args.workdir / f"{stem}_defs.lean", args.workdir / f"{stem}.lean"
    defs.write_text(lean_source(family, n, orig, opt, mut, False, args.chunk, witness))
    full.write_text(lean_source(family, n, orig, opt, mut, True, args.chunk, witness))
    if not args.no_lean and rec["in_fragment"]:
        rec["defs"] = run_lean(defs, args.timeout)
        rec["full"] = run_lean(full, args.timeout)
        if rec["defs"]["status"] == "ok" and rec["full"]["status"] == "ok":
            rec["kernel_s"] = round(rec["full"]["wall_s"] - rec["defs"]["wall_s"], 1)
    return rec


def key(rec: dict) -> tuple:
    """What identifies a run: a rerun replaces the record with the same key."""
    return (rec["family"], rec.get("pipeline"), rec.get("chunk", 0), rec["qubits"], rec["gates"])


def markdown_table(records: list[dict]) -> str:
    """The results as a Markdown table."""
    lines = ["| Family | Pipeline | Qubits | Gates | T-count | Optimised gates | Chunk | "
             "Defs only | With theorems | Kernel share | Peak memory | Status |",
             "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|"]
    for r in records:
        d, f = r.get("defs", {}), r.get("full", {})
        pipeline = r.get("pipeline") or DEFAULT_PIPELINE[r["family"]]
        family = r["family"] + (f" ×{r['rounds']}" if "rounds" in r else "")
        lines.append(
            f"| {family} | {pipeline} | {r['qubits']} | {r['gates']} | "
            f"{r['tcount']} → {r['opt_tcount']} | {r['opt_gates']} | {r.get('chunk', 0) or '—'} | "
            f"{d.get('wall_s', '—')} s | {f.get('wall_s', '—')} s | "
            f"{r.get('kernel_s', '—')} s | {f.get('max_rss_gb', '—')} GB | "
            f"{f.get('status', 'not run')} |")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--family", choices=sorted(DEFAULT_PIPELINE), required=True)
    parser.add_argument("--sizes", nargs="+", type=int, required=True,
                        help="qubit counts (code distances for `surface`)")
    parser.add_argument("--pipeline", choices=["full_reduce", "teleport", "basic"])
    parser.add_argument("--chunk", type=int, default=0,
                        help="tableau generators per declaration; 0 is one declaration")
    parser.add_argument("--rounds", type=int, default=2, help="syndrome rounds for `surface`")
    parser.add_argument("--gates-per-qubit", type=int, default=10)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--no-lean", action="store_true")
    parser.add_argument("--table", action="store_true")
    args = parser.parse_args()
    if zx.__version__ != "0.9.0":
        raise RuntimeError(f"Expected PyZX 0.9.0, found {zx.__version__}")
    records = json.loads(args.results.read_text()) if args.results.exists() else []
    if args.table:
        print(markdown_table(records))
        return
    for size in args.sizes:
        rec = run_size(args, size)
        records = [r for r in records if key(r) != key(rec)] + [rec]
        args.results.write_text(json.dumps(records, indent=1) + "\n")
        print(f"{rec['family']}/{rec['pipeline']} n={rec['qubits']}: {rec['gates']} -> "
              f"{rec['opt_gates']} gates, T {rec['tcount']} -> {rec['opt_tcount']}, "
              f"fragment={rec['in_fragment']}, mirror={rec.get('mirror_agrees')}, "
              f"witness={rec.get('mutant_witness')}, defs={rec.get('defs', {}).get('wall_s')} s, "
              f"full={rec.get('full', {})}", flush=True)


if __name__ == "__main__":
    main()
