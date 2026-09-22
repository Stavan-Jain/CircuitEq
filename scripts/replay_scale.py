"""Measure bounded replay on long, move-only certificates.

A rotation of distinct-wire H gates has exactly ``moves`` moveLeft steps,
with no cancellation or window oracle. This isolates replay from search for
an alignment and from exponential basis evaluation. Uses the same timing
helper as the other scale scripts (macOS /usr/bin/time -l).

Example::

    python3 scripts/replay_scale.py --gates 128 512 1024 --moves 128 \
        --workdir /tmp/replay-scale

``--chunk 0`` selects the former single-replay closing form. Results are
written to results.json in the work directory; they are measurements, not a
claim that arbitrary circuits of these sizes can be aligned.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from chunks import CHUNK_HEADER, run_lean


def circuit(gates: list[int]) -> str:
    """Format a literal circuit with bounded source line lengths."""
    lines = []
    for start in range(0, len(gates), 8):
        lines.append(", ".join(f"H {i}" for i in gates[start:start + 8]))
    return "[" + ",\n    ".join(lines) + "]"


def lean_source(gates: int, moves: int, chunk: int) -> str:
    """Distinct wires ensure the prescribed cyclic rotation is licensed."""
    if gates < 2 or not 0 < moves < gates or chunk < 0:
        raise ValueError("require gates >= 2, 0 < moves < gates, chunk >= 0")
    original = list(range(gates))
    optimized = original[-moves:] + original[:-moves]
    return f"""import CircuitEq.Tactic
open Quantum Quantum.Circuit Instr
{CHUNK_HEADER}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option circuit.replayChunkSize {chunk}

def original : Circuit {gates} :=
  {circuit(original)}

def optimized : Circuit {gates} :=
  {circuit(optimized)}

set_option trace.profiler true in
set_option profiler.threshold 0 in
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_simp
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--gates", type=int, nargs="+", default=[128, 512, 1024])
    parser.add_argument("--moves", type=int, default=128,
                        help="moves per pair, capped at half its gates")
    parser.add_argument("--chunk", type=int, default=8)
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--no-lean", action="store_true")
    args = parser.parse_args()
    if min(args.gates) < 2 or args.moves < 1 or args.chunk < 0 or args.timeout <= 0:
        parser.error("require gates >= 2, moves >= 1, chunk >= 0 and timeout > 0")
    args.workdir.mkdir(parents=True, exist_ok=True)
    records = []
    for gates in args.gates:
        moves = min(args.moves, gates // 2)
        path = args.workdir / f"replay_g{gates}_m{moves}_c{args.chunk}.lean"
        path.write_text(lean_source(gates, moves, args.chunk))
        rec = {"gates": gates, "moves": moves, "chunk": args.chunk, "file": str(path)}
        if not args.no_lean:
            rec.update(run_lean(path, args.timeout))
        records.append(rec)
        print(json.dumps(rec), flush=True)
        (args.workdir / "results.json").write_text(json.dumps(records, indent=2) + "\n")
    if any(r.get("status", "ok") != "ok" for r in records):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
