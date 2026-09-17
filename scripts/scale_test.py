"""Scale test: the fragment checkers on larger circuits.

Generates seeded random circuits of increasing size, optimises them with
PyZX, and asks the kernel to certify each pair with the checker for its
fragment, measuring wall time and peak memory of the Lean process:

* ``clifford``: gates ``H``, ``S``, ``CX`` on ``n`` qubits, ``g`` gates;
  optimised by ``full_reduce`` + extraction + ``basic_optimization`` (a
  re-synthesis); certified by ``tableauChecker n`` (``≡ₛ``).
* ``cnot_t``: gates ``CX`` and ``T`` on ``n`` qubits; optimised by
  ``teleport_reduce`` + ``basic_optimization`` (phase folding); certified
  by ``phasePolyChecker n`` (``≡ᵤ``) when the output stays in the fragment.

For every pair a *mutant* (one gate of the optimised circuit deleted) is
also checked: the checker must return ``false`` on it. Two Lean files are
produced per size, one with only the definitions (elaboration cost) and
one with the theorems (elaboration plus kernel), so the kernel's share is
the difference. Requires pyzx==0.9.0. Results go to a JSON file; ``--table``
prints them as Markdown.
"""

import argparse
import json
import random
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_pyzx_benchmarks as cpb  # noqa: E402

import pyzx as zx  # noqa: E402
from pyzx.circuit.gates import CNOT, HAD, S, T  # noqa: E402

FRAGMENT_DIAG = {"Z", "S", "Sdg", "T", "Tdg"}


def random_circuit(family: str, n: int, gates: int, seed: int) -> zx.Circuit:
    """A seeded random circuit of the family on ``n`` qubits."""
    rng = random.Random(seed)
    c = zx.Circuit(n)
    for _ in range(gates):
        if family == "clifford":
            kind = rng.choice(["H", "S", "CX", "CX"])
        else:
            kind = rng.choice(["T", "CX", "CX"])
        if kind == "CX":
            a, b = rng.sample(range(n), 2)
            c.gates.append(CNOT(a, b))
        elif kind == "H":
            c.gates.append(HAD(rng.randrange(n)))
        elif kind == "S":
            c.gates.append(S(rng.randrange(n)))
        else:
            c.gates.append(T(rng.randrange(n)))
    return c


def in_fragment(instrs: list[str], family: str) -> bool:
    """Whether every instruction is in the checker's fragment."""
    for ins in instrs:
        name = ins.split()[0]
        if family == "clifford":
            if name not in {"H", "X", "Y", "Z", "S", "Sdg", "CX"}:
                return False
        elif name != "CX" and name not in FRAGMENT_DIAG:
            return False
    return True


def lean_list(instrs: list[str]) -> str:
    """Format instructions as a Lean list literal, eight per line."""
    rows = [", ".join(instrs[i:i + 8]) for i in range(0, len(instrs), 8)]
    return "[" + ",\n    ".join(rows) + "]"


def lean_source(family: str, n: int, orig: list[str], opt: list[str], mut: list[str],
                theorems: bool) -> str:
    """The Lean file for one pair."""
    module = "CircuitEq.Tableau" if family == "clifford" else "CircuitEq.PhasePoly"
    checker = f"tableauChecker {n}" if family == "clifford" else f"phasePolyChecker {n}"
    rel = "≡ₛ" if family == "clifford" else "≡ᵤ"
    out = [f"import {module}", "open Quantum Quantum.Circuit Instr", "",
           f"def original : Circuit {n} :=\n  {lean_list(orig)}", "",
           f"def optimized : Circuit {n} :=\n  {lean_list(opt)}", "",
           f"def mutant : Circuit {n} :=\n  {lean_list(mut)}", ""]
    if theorems:
        out += [f"theorem equiv : original {rel} optimized :=",
                f"  ({checker}).sound _ _ (by decide +kernel)", ""]
        if family == "clifford":
            out += [f"theorem mutant_rejected : ({checker}).check original mutant = false := by",
                    "  decide +kernel", ""]
        else:
            # the phase-polynomial checker is complete on its fragment, so a mutant
            # is refuted, not merely undecided
            out += ["theorem mutant_refuted : ¬ (original ≡ᵤ mutant) :=",
                    "  phasePolyRefutes_sound (by decide +kernel)", ""]
    return "\n".join(out)


def run_lean(path: Path, timeout: float) -> dict:
    """Run ``lake env lean`` on a file with a time cap; return time, memory, status."""
    cmd = ["/usr/bin/time", "-l", "perl", "-e", "alarm shift @ARGV; exec @ARGV",
           str(int(timeout)), "lake", "env", "lean", str(path)]
    t0 = time.time()
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    wall = time.time() - t0
    out = proc.stdout + proc.stderr
    rss = re.search(r"(\d+)\s+maximum resident set size", out)
    errors = [l for l in out.splitlines() if "error" in l]
    status = "ok" if proc.returncode == 0 and not errors else (
        "timeout" if wall >= timeout - 1 else "error")
    return {"status": status, "wall_s": round(wall, 1),
            "max_rss_gb": round(int(rss.group(1)) / 2**30, 2) if rss else None,
            "errors": errors[:3]}


def run_size(family: str, n: int, gates: int, seed: int, workdir: Path,
             timeout: float, lean: bool) -> dict:
    """Generate, optimise, emit and (optionally) check one size."""
    original = random_circuit(family, n, gates, seed)
    pipeline = "full_reduce" if family == "clifford" else "teleport"
    optimized = cpb.optimize(original, pipeline)
    orig, opt = cpb.lean_instructions(original), cpb.lean_instructions(optimized)
    rng = random.Random(seed + 1)
    idx = rng.randrange(len(opt))
    mut = opt[:idx] + opt[idx + 1:]
    rec = {"family": family, "qubits": n, "gates": len(orig), "opt_gates": len(opt),
           "tcount": original.tcount(), "opt_tcount": optimized.tcount(),
           "in_fragment": in_fragment(opt, family), "deleted": opt[idx], "seed": seed}
    workdir.mkdir(parents=True, exist_ok=True)
    stem = f"{family}_n{n}_g{gates}_s{seed}"
    defs = workdir / f"{stem}_defs.lean"
    full = workdir / f"{stem}.lean"
    defs.write_text(lean_source(family, n, orig, opt, mut, theorems=False))
    full.write_text(lean_source(family, n, orig, opt, mut, theorems=True))
    if lean and rec["in_fragment"]:
        rec["defs"] = run_lean(defs, timeout)
        rec["full"] = run_lean(full, timeout)
        if rec["defs"]["status"] == "ok" and rec["full"]["status"] == "ok":
            rec["kernel_s"] = round(rec["full"]["wall_s"] - rec["defs"]["wall_s"], 1)
    return rec


def markdown_table(records: list[dict]) -> str:
    """The results as a Markdown table."""
    lines = ["| Family | Qubits | Gates | T-count | Optimised gates | In fragment | "
             "Defs only | With theorems | Kernel share | Peak memory | Status |",
             "|---|---:|---:|---:|---:|---|---:|---:|---:|---:|---|"]
    for r in records:
        d, f = r.get("defs", {}), r.get("full", {})
        lines.append(
            f"| {r['family']} | {r['qubits']} | {r['gates']} | {r['tcount']} → {r['opt_tcount']} | "
            f"{r['opt_gates']} | {'yes' if r['in_fragment'] else 'no'} | "
            f"{d.get('wall_s', '—')} s | {f.get('wall_s', '—')} s | "
            f"{r.get('kernel_s', '—')} s | {f.get('max_rss_gb', '—')} GB | "
            f"{f.get('status', 'not run')} |")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--family", choices=["clifford", "cnot_t"], required=True)
    parser.add_argument("--sizes", nargs="+", type=int, required=True, help="qubit counts")
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
    for n in args.sizes:
        rec = run_size(args.family, n, args.gates_per_qubit * n, args.seed, args.workdir,
                       args.timeout, not args.no_lean)
        records = [r for r in records if not (r["family"] == rec["family"]
                                              and r["qubits"] == rec["qubits"]
                                              and r["gates"] == rec["gates"])]
        records.append(rec)
        args.results.write_text(json.dumps(records, indent=1) + "\n")
        print(f"{rec['family']} n={n}: {rec['gates']} -> {rec['opt_gates']} gates, "
              f"T {rec['tcount']} -> {rec['opt_tcount']}, fragment={rec['in_fragment']}, "
              f"defs={rec.get('defs', {}).get('wall_s')} s, full={rec.get('full', {})}",
              flush=True)


if __name__ == "__main__":
    main()
