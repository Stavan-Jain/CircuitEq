"""Chunked basis decide for a benchmark pair: one theorem per range of basis vectors.

``decide +kernel`` on ``original ≡ᵤ optimized`` evaluates all ``2 ^ n`` basis
vectors in one declaration and the kernel keeps every memoised amplitude
until it ends, which runs the seven-qubit ``SteanePlus`` pair out of memory
(``benchmarks/scale/README.md``, "The basis evaluator"). This script emits
the same decision as one theorem per range of basis vectors
(``checkEquivAt``, ``CircuitEq/Decide.lean``), assembled by
``equivalent_of_allBelow``, runs it, and reports time and peak memory.

Usage::

    python scripts/chunked_decide.py SteanePlus --chunk 16 --workdir /tmp/chunked
    python scripts/chunked_decide.py Tof3 --phase 0     # up to the phase ω^0

The module is a ``CircuitEq/Benchmarks`` module name; its ``original`` and
``optimized`` are used as they stand. No dependencies beyond the standard
library.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from chunks import CHUNK_HEADER, ROOT, chunk_theorems, run_lean


def lean_source(module: str, n: int, chunk: int, phase: int | None) -> str:
    """The Lean file: chunk theorems and the assembled equivalence."""
    if phase is None:
        pred, rel, close = "checkEquivAt original optimized", "≡ᵤ", "equivalent_of_allBelow"
    else:
        pred, rel = f"checkEquivUpToPhaseAt original optimized {phase}", "≡ₚ"
        close = "equivalentUpToPhase_of_allBelow (by decide)"
    lines, term = chunk_theorems(pred, 2 ** n, chunk, "r")
    out = [f"import CircuitEq.Benchmarks.{module}",
           f"open Quantum Quantum.Circuit Quantum.Circuit.Benchmarks.{module}", "",
           CHUNK_HEADER, ""]
    out += lines
    out += [f"theorem chunked : original {rel} optimized :=", f"  {close} ({term})", ""]
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("module", help="a CircuitEq/Benchmarks module, e.g. SteanePlus")
    parser.add_argument("--chunk", type=int, default=16, help="basis vectors per declaration")
    parser.add_argument("--phase", type=int, default=None, help="prove ≡ₚ with the phase ω^k")
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--no-lean", action="store_true")
    args = parser.parse_args()
    src = (ROOT / "CircuitEq" / "Benchmarks" / f"{args.module}.lean").read_text()
    match = re.search(r"def original : Circuit (\d+) :=", src)
    if match is None:
        raise ValueError(f"{args.module}: missing def original")
    n = int(match[1])
    args.workdir.mkdir(parents=True, exist_ok=True)
    path = args.workdir / f"chunked_{args.module}_c{args.chunk}.lean"
    path.write_text(lean_source(args.module, n, args.chunk, args.phase))
    print(f"{args.module}: {n} qubits, {2 ** n} basis vectors, "
          f"{-(-2 ** n // args.chunk)} declarations of {args.chunk} -> {path}")
    if not args.no_lean:
        print(run_lean(path, args.timeout))


if __name__ == "__main__":
    main()
