"""Chunked kernel evaluation: emit one theorem per range, time a Lean file.

The Lean kernel keeps its reduction cache for the whole of one declaration,
so a long ``decide +kernel`` runs out of memory before it runs out of time
(``CircuitEq/Chunk.lean``). A check that is a conjunction over the indices
``0 .. total - 1`` is instead emitted as one theorem per range of indices,
assembled by ``AllBelow.add``. This module has no dependencies, so both the
PyZX-based scale test and the benchmark-module script can use it.
"""

from __future__ import annotations

import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Chunking only bounds memory with asynchronous elaboration off: by default each
# theorem is checked in a task whose memory is not returned before the next one
# starts (measured: sixteen 4-vector declarations peak at 3.6 GB with it on and
# at 2.6 GB, the footprint of one, with it off).
CHUNK_HEADER = "set_option Elab.async false"


def chunk_theorems(pred: str, total: int, chunk: int, prefix: str) -> tuple[list[str], str]:
    """Theorems ``(List.range' lo len).all (pred) = true`` covering ``0 .. total - 1``.

    Returns the theorem source lines and the ``AllBelow (pred) total`` proof
    term that assembles them. The term nests one application per chunk, so
    very many chunks are grouped into intermediate theorems of 64.
    """
    lines, names = [], []
    for k, lo in enumerate(range(0, total, chunk)):
        length = min(chunk, total - lo)
        names.append(f"{prefix}{k}")
        lines += [f"theorem {prefix}{k} : (List.range' {lo} {length}).all ({pred}) = true := by",
                  "  decide +kernel", ""]
    term, done = "AllBelow.zero _", 0
    for g, start in enumerate(range(0, len(names), 64)):
        group = names[start:start + 64]
        for name in group:
            term = f"({term}).add {name}"
        done = min(total, (start + len(group)) * chunk)
        if start + 64 < len(names):
            lines += [f"theorem {prefix}_upto{g} : AllBelow ({pred}) {done} :=", f"  {term}", ""]
            term = f"{prefix}_upto{g}"
    return lines, term


def run_lean(path: Path, timeout: float) -> dict:
    """Run ``lake env lean`` on a file with a time cap; return time, memory, status."""
    cmd = ["/usr/bin/time", "-l", "perl", "-e", "alarm shift @ARGV; exec @ARGV",
           str(int(timeout)), "lake", "env", "lean", str(path)]
    t0 = time.time()
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    wall = time.time() - t0
    out = proc.stdout + proc.stderr
    rss = re.search(r"(\d+)\s+maximum resident set size", out)
    errors = [line for line in out.splitlines() if "error" in line]
    status = "ok" if proc.returncode == 0 and not errors else (
        "timeout" if wall >= timeout - 1 else "error")
    return {"status": status, "wall_s": round(wall, 1),
            "max_rss_gb": round(int(rss.group(1)) / 2**30, 2) if rss else None,
            "errors": errors[:3]}
