#!/usr/bin/env python3
"""Agent harness for the equivalence-checking task (draft, `QUEUE.md` item 1).

A task is a pair of Clifford+T circuits. The harness gives an agent a warm
copy of the library with the answer held out, one fixed prompt, a wall-clock
budget and a memory limit, and asks for a Lean proof that the pair is
equivalent or a Lean proof that it is not. The Lean kernel is the judge, so a
task needs no ground truth.

What is fixed and what varies (every result row records all of them):

* the harness: this script, `benchmarks/harness/PROMPT.md`, the agent
  configuration under `benchmarks/harness/agents/`;
* the library: a commit, built once by `prepare` and cloned for every run,
  together with `PLAYBOOK.md`, the prover's guide that is versioned with the
  library and installed as the run's `CLAUDE.md`;
* the model.

Commands:

    tasks                         list the tasks
    import-benchmark MODULE       make a task from `CircuitEq/Benchmarks/MODULE.lean`
    import-pair FILE              make a task from a JSON file of two gate lists
    prepare [--commit REV]        build the warm base for a library commit (runs lake)
    setup TASK                    make a run workspace and stop (inspect it, or run by hand)
    run TASK                      setup, agent, judge, record
    judge RUN                     judge a finished run again
    record RUN                    judge and record a run whose harness process died
    digest RUN                    what the agent said and did, one line per step
    selftest                      check the parts that need neither lake nor an agent

Inside a run workspace the agent sees two commands, `./submit equiv|not_equiv`
(the judge, so "done" is unambiguous) and `./time-left`.

The judge in this draft: no file that existed at the start may change except
`Solution.lean`; the agent's Lean sources may not contain `native_decide`,
`debug.*` options or the other compiler-trust routes; the harness writes its
own restatement of the claim, with fully qualified names and no notation,
whose proof is the agent's theorem, so it typechecks only if the agent proved
exactly that statement about exactly the harness's circuits; and that
restatement may depend only on the three standard axioms; and the solution's
modules are replayed through the kernel by `leanchecker`, which is what catches a
declaration that skipped it (`debug.skipKernelTC`). The text scan is an early
warning and not a defence. The harness also writes `changes.diff` for a person to
read: the replay trusts the library and mathlib as built, and it is the same
kernel again, not an independent checker (SafeVerify, `leanprover/comparator`:
`QUEUE.md`, "Later").

Lake is only ever run in a workspace whose `.lake/packages` resolves to a
directory with a compiled mathlib at the revisions of `lake-manifest.json`;
otherwise lake would clone or rebuild mathlib. The harness refuses instead.

`scripts/optimizer_harness.py`, the harness for the optimisation task, imports
this module for everything the two share (bases, lake guards, the watchdog,
workspace setup and hold-out, the manifest, the judge of `equiv`, the agent
launch, the results row), and a copy of this file runs inside every workspace
of both. Keep the functions it calls backward compatible.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from pathlib import Path

HARNESS_VERSION = "0.6-draft"

SCRIPT = Path(__file__).resolve()
ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# Relation key -> (constant in `Quantum.Circuit`, notation, words for the prompt).
RELATIONS = {
    "u": ("Equivalent", "≡ᵤ", "equal as unitaries (`≡ᵤ`)"),
    "p": ("EquivalentUpToPhase", "≡ₚ", "equal up to a global phase (`≡ₚ`)"),
    "s": ("EquivalentUpToScalar", "≡ₛ", "equal up to a nonzero scalar (`≡ₛ`)"),
}
CLAIMS = ("equiv", "not_equiv")

# The modules the `core` configuration keeps: the semantics and nothing else.
CORE_MODULES = ("Zeta8", "Bits", "Gates", "Dyadic", "Chunk", "Semantics", "Relations", "Decide")

# Removed from every run workspace: documents that quote benchmark proofs, and
# fixtures that record alignments. `CLAUDE.md` is replaced by the playbook.
GLOBAL_DELETE = ("README.md", "ROADMAP.md", "QUEUE.md", "CLAUDE.md", "benchmarks", ".github")
# `scripts/certificate.py` lists the windows of two benchmark proofs.
GLOBAL_REDACT = (
    {"file": "scripts/certificate.py", "pattern": r"^BENCHMARKS = \{.*?^\}",
     "replacement": "BENCHMARKS = {}", "flags": "ms"},
)

# The judge's scratch module (a solution may not import it), where the optimisation harness
# keeps its copies of accepted submissions, and how long one judge build or replay may take.
JUDGE_FILE = "Harness/Judge.lean"
ACCEPTED_DIR = ".harness/accepted"
JUDGE_TIMEOUT_S = 1800
# Never part of the manifest: build output, the copies the optimisation harness keeps of
# accepted submissions, the judge's scratch file, the log `./submit` appends to.
MANIFEST_SKIP_DIRS = (".lake", ACCEPTED_DIR)
MANIFEST_SKIP_FILES = (JUDGE_FILE, ".harness/submissions.jsonl", ".harness/run.json",
                       ".harness/submit.log", ".harness/manifest.json")
EDITABLE = ("Solution.lean",)

# Text the agent's Lean sources may not contain (comments are stripped first).
REJECT_PATTERNS = (
    (re.compile(r"\bnative_decide\b"), "`native_decide`"),
    (re.compile(r"\bdebug\.[A-Za-z]"),
     "a `debug.*` option (`debug.skipKernelTC` skips the kernel)"),
    (re.compile(r"\b(ofReduceBool|reduceBool|ofReduceNat|reduceNat|trustCompiler)\b"),
     "a compiler-trust primitive"),
    (re.compile(r"^\s*(private\s+|protected\s+)?axiom\b", re.M), "an `axiom` declaration"),
    (re.compile(r"\bimplemented_by\b|@\[\s*extern\b"), "`implemented_by` / `extern`"),
)
# Not rejected, but listed for the person who reads the diff.
WARN_PATTERNS = (
    (re.compile(r"\bset_option\s+"
                r"(?!(?:Elab\.async|maxRecDepth|maxHeartbeats|trace\.|pp\.|linter\.)[\w.]*\b)"),
     "a `set_option` other than Elab.async, maxRecDepth, maxHeartbeats, trace.*, pp.*, linter.*"),
    (re.compile(r"\bunsafe\b"), "`unsafe`"),
    (re.compile(r"\brun_cmd\b|\brun_elab\b|\brun_meta\b|#eval\b"), "code run at elaboration time"),
    (re.compile(r"\bIO\.(Process|FS)\b"), "process or file-system access from Lean"),
    (re.compile(r"\binitialize\b|\bbuiltin_initialize\b"), "`initialize`"),
    (re.compile(r"\b(local\s+|scoped\s+)?"
                r"(notation|infix|infixl|infixr|prefix|postfix|macro_rules)\b"),
     "new notation or macro rules"),
)

GATE_RE = re.compile(r"^(?:(?:H|X|Y|Z|S|Sdg|T|Tdg) \d+|CX \d+ \d+)$")


class HarnessError(RuntimeError):
    """A condition under which the harness refuses to continue."""


# --------------------------------------------------------------------------
# Paths
# --------------------------------------------------------------------------

def repo_root() -> Path:
    """The repository this script belongs to (not valid for the in-run copy)."""
    return SCRIPT.parents[1]


def harness_dir() -> Path:
    return repo_root() / "benchmarks" / "harness"


def harness_home() -> Path:
    return Path(os.environ.get("CIRCUITEQ_HARNESS_HOME", "~/.circuiteq-harness")).expanduser()


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def git(*args: str, cwd: Path | None = None) -> str:
    out = subprocess.run(["git", *args], cwd=cwd or repo_root(), check=True,
                         capture_output=True, text=True)
    return out.stdout.strip()


# --------------------------------------------------------------------------
# Lean text
# --------------------------------------------------------------------------

def fmt_lean_list(gates: list[str], indent: int = 4, width: int = 96) -> str:
    """`[g, g, ...]` wrapped at `width` columns, continuation lines indented."""
    if not gates:
        return "[]"
    lines, cur = [], "["
    for k, g in enumerate(gates):
        piece = g + ("]" if k == len(gates) - 1 else ",")
        sep = "" if cur in ("[", " " * indent) else " "
        if len(cur) + len(sep) + len(piece) > width - 2 and cur.strip() not in ("[", ""):
            lines.append(cur)
            cur, sep = " " * indent, ""
        cur += sep + piece
    lines.append(cur)
    return "\n".join(lines)


def read_circuit_def(path: Path, name: str) -> tuple[int, list[str]]:
    """The width and the gate strings of `def name : Circuit n := [...]` in a Lean file."""
    m = re.search(rf"def {name} : Circuit (\d+) :=\s*\[([^\]]*)\]", path.read_text())
    if m is None:
        raise HarnessError(f"{path}: no `def {name} : Circuit n := [...]`")
    gates = [" ".join(g.split()) for g in m[2].split(",") if g.strip()]
    for g in gates:
        if not GATE_RE.match(g):
            raise HarnessError(f"{path}: cannot read the gate `{g}`")
    return int(m[1]), gates


def read_benchmark_defs(module: Path) -> tuple[int, list[str], list[str]]:
    """The `original` and `optimized` lists of a benchmark module, as gate strings."""
    n, original = read_circuit_def(module, "original")
    m, optimized = read_circuit_def(module, "optimized")
    if n != m:
        raise HarnessError(f"{module}: the two circuits have different widths")
    return n, original, optimized


TASK_LEAN = """\
import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit {n} :=
  {original}

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit {n} :=
  {optimized}

end Quantum.Circuit.Harness
"""

SOLUTION_LEAN = """\
import CircuitEq
import Harness.Task

/-! # Solution

Prove exactly one of the two theorems below. Then run `./submit equiv` or
`./submit not_equiv`.

Lemmas may go in this file, and new modules under `Solution/` (import them
here). No other existing file may be edited.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The claim holds. -/
theorem equiv : original {sym} optimized := by
  sorry

/-- The claim fails. -/
theorem not_equiv : ¬ (original {sym} optimized) := by
  sorry

end Quantum.Circuit.Harness
"""

JUDGE_LEAN = """\
import Harness.Task
import Solution

/-! Written by the harness when it judges. The claim is restated against the
harness's own circuits, with fully qualified names and no notation, and
proved by the solution's theorem: it typechecks only if the solution proves
exactly this statement. -/

theorem Quantum.Circuit.Harness.Judge.verdict :
    {statement} :=
  Quantum.Circuit.Harness.{claim}

#print axioms Quantum.Circuit.Harness.Judge.verdict
"""

LAKEFILE_PATCH = """
# --- added by the agent harness ---
[[lean_lib]]
name = "Harness"

[[lean_lib]]
name = "Solution"
"""

PYTHON_SH = """\
#!/bin/sh
# A Python that has numpy and pyzx, which the library's scripts import.
exec "{python}" "$@"
"""

TZAP_SH = """\
#!/bin/sh
# The TZAP circuit optimiser (github.com/qqq-wisc/tzap): an untrusted oracle. What it
# returns proves nothing and may equal its input only up to a global phase.
exec "{tzap}" "$@"
"""

SUBMIT_SH = """\
#!/bin/sh
# The judge. Usage: ./submit equiv   or   ./submit not_equiv
here="$(cd "$(dirname "$0")" && pwd)"
exec python3 "$here/.harness/agent_harness.py" submit --ws "$here" "$@"
"""

TIME_LEFT_SH = """\
#!/bin/sh
# Wall-clock time left in this run.
here="$(cd "$(dirname "$0")" && pwd)"
exec python3 "$here/.harness/agent_harness.py" time-left --ws "$here"
"""


def judge_statement(relation: str, claim: str) -> str:
    const = RELATIONS[relation][0]
    body = (f"Quantum.Circuit.{const} Quantum.Circuit.Harness.original "
            "Quantum.Circuit.Harness.optimized")
    return body if claim == "equiv" else f"¬ {body}"


def strip_lean_comments(src: str) -> str:
    """Remove `--` line comments and nested `/- -/` block comments."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        elif depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def scan_lean(path: Path, rel: str) -> tuple[list[str], list[str]]:
    """Reasons to reject and things to look at, for one agent-written file."""
    text = strip_lean_comments(path.read_text(errors="replace"))
    rejects = [f"{rel}: uses {what}" for rx, what in REJECT_PATTERNS if rx.search(text)]
    warns = [f"{rel}: {what}" for rx, what in WARN_PATTERNS if rx.search(text)]
    return rejects, warns


IMPORT_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)", re.M)


def solution_files(ws: Path) -> list[str]:
    """The files of a submission: `Solution.lean` and everything under `Solution/`."""
    rels = ["Solution.lean"] if (ws / "Solution.lean").is_file() else []
    if (ws / "Solution").is_dir():
        rels += sorted(str(p.relative_to(ws)) for p in (ws / "Solution").rglob("*")
                       if p.is_file() and "__pycache__" not in p.parts)
    return rels


def foreign_imports(ws: Path, manifest: dict[str, str]) -> list[str]:
    """Reasons to reject: a solution module importing Lean code of this workspace that is
    neither a file that existed at the start nor under `Solution/`. The kernel replay covers
    the `Solution` modules only, so a lemma that skipped the kernel in any other new module
    (or in the judge's own scratch module) would never be replayed: a false claim was
    accepted that way before this rule (19 September 2026)."""
    reasons = []
    for rel in solution_files(ws):
        if not rel.endswith(".lean"):
            continue
        text = strip_lean_comments((ws / rel).read_text(errors="replace"))
        for module in IMPORT_RE.findall(text):
            path = str(module_path(module))
            if module.split(".")[0] != "Solution" and path not in manifest and (ws / path).exists():
                reasons.append(f"{rel}: imports `{module}`, which is neither part of the workspace "
                               "as given nor under `Solution/`; move it under `Solution/`")
    return reasons


def parse_axioms(output: str, name: str) -> list[str] | None:
    """The axiom list `#print axioms name` printed, or `None` if it printed none."""
    if f"'{name}' does not depend on any axioms" in output:
        return []
    m = re.search(re.escape(f"'{name}' depends on axioms:") + r"\s*\[(.*?)\]", output, re.S)
    if m is None:
        return None
    return [a.strip() for a in m[1].split(",") if a.strip()]


# --------------------------------------------------------------------------
# Tasks
# --------------------------------------------------------------------------

def tasks_dir() -> Path:
    return harness_dir() / "tasks"


def task_dirs() -> list[Path]:
    if not tasks_dir().exists():
        return []
    return sorted(p for p in tasks_dir().iterdir() if (p / "task.json").exists())


def load_task(name: str) -> dict:
    path = tasks_dir() / name / "task.json"
    if not path.exists():
        raise HarnessError(f"no task `{name}` (looked for {path})")
    task = json.loads(path.read_text())
    task["dir"] = str(path.parent)
    if task["relation"] not in RELATIONS:
        raise HarnessError(f"{path}: unknown relation {task['relation']!r}")
    return task


def cmd_tasks(_args) -> None:
    rows = []
    for d in task_dirs():
        t = json.loads((d / "task.json").read_text())
        rows.append((t["name"], t["qubits"], f"{t['gates'][0]}/{t['gates'][1]}",
                     RELATIONS[t["relation"]][1], t.get("expected", "?"), t.get("split", "?")))
    print(f"{'task':28} {'n':>3} {'gates':>9} rel  {'expected':10} split")
    for r in rows:
        print(f"{r[0]:28} {r[1]:>3} {r[2]:>9} {r[3]:4} {r[4]:10} {r[5]}")


def cmd_import_benchmark(args) -> None:
    module = repo_root() / "CircuitEq" / "Benchmarks" / f"{args.module}.lean"
    n, original, optimized = read_benchmark_defs(module)
    name = args.name
    task = {
        "name": name, "qubits": n, "relation": args.relation, "expected": "equiv",
        "split": "dev", "family": args.family or name, "rung": args.rung,
        "source": {"module": f"CircuitEq/Benchmarks/{args.module}.lean",
                   "pipeline": args.pipeline or ""},
        "holdout": {"modules": [f"CircuitEq.Benchmarks.{args.module}"], "redact": []},
        "known_leaks": [],
    }
    if args.mutant is not None:
        rng = random.Random(args.mutant)
        k = rng.randrange(len(optimized))
        task.update(name=f"{name}_mut{args.mutant}", expected="not_equiv",
                    mutation={"side": "optimized", "deleted_index": k,
                              "deleted_gate": optimized[k], "seed": args.mutant})
        optimized = optimized[:k] + optimized[k + 1:]
    task["gates"] = [len(original), len(optimized)]
    out = tasks_dir() / task["name"]
    out.mkdir(parents=True, exist_ok=True)
    old = out / "task.json"
    if old.exists():  # keep the hand-written fields of an existing task
        prev = json.loads(old.read_text())
        task["known_leaks"] = prev.get("known_leaks", [])
        task["holdout"]["redact"] = prev.get("holdout", {}).get("redact", [])
    (out / "task.json").write_text(json.dumps(task, indent=2, ensure_ascii=False) + "\n")
    (out / "Task.lean").write_text(
        TASK_LEAN.replace("{n}", str(n))
        .replace("{original}", fmt_lean_list(original))
        .replace("{optimized}", fmt_lean_list(optimized)))
    print(f"wrote {out.relative_to(repo_root())}/ ({n} qubits, {task['gates']} gates)")


def cmd_import_pair(args) -> None:
    """A task from a JSON file: name, qubits, original, optimized, and optional metadata."""
    pair = json.loads(Path(args.file).read_text())
    for side in ("original", "optimized"):
        for g in pair[side]:
            if not GATE_RE.match(g):
                raise HarnessError(f"{args.file}: cannot read the gate `{g}`")
            if any(int(w) >= pair["qubits"] for w in g.split()[1:]):
                raise HarnessError(f"{args.file}: `{g}` is off a register of {pair['qubits']}")
    task = {
        "name": pair["name"], "qubits": pair["qubits"], "relation": pair.get("relation", "u"),
        "expected": pair.get("expected", "unknown"), "split": pair.get("split", "held-out"),
        "family": pair.get("family", pair["name"]), "rung": pair.get("rung"),
        "source": pair.get("source", {}),
        "holdout": {"modules": [], "redact": [], "delete": pair.get("holdout_delete", [])},
        "known_leaks": pair.get("known_leaks", []),
        "gates": [len(pair["original"]), len(pair["optimized"])],
    }
    out = tasks_dir() / task["name"]
    out.mkdir(parents=True, exist_ok=True)
    (out / "task.json").write_text(json.dumps(task, indent=2, ensure_ascii=False) + "\n")
    (out / "Task.lean").write_text(
        TASK_LEAN.replace("{n}", str(pair["qubits"]))
        .replace("{original}", fmt_lean_list(pair["original"]))
        .replace("{optimized}", fmt_lean_list(pair["optimized"])))
    print(f"wrote {out.relative_to(repo_root())}/ ({task['qubits']} qubits, {task['gates']} gates)")


# --------------------------------------------------------------------------
# Lake, guarded
# --------------------------------------------------------------------------

def compiled_mathlib(packages: Path) -> bool:
    return (packages / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean").exists()


def find_packages(explicit: str | None) -> Path:
    """A packages directory with a compiled mathlib, or refuse."""
    candidates = []
    if explicit:
        candidates.append(Path(explicit))
    if os.environ.get("CIRCUITEQ_PACKAGES"):
        candidates.append(Path(os.environ["CIRCUITEQ_PACKAGES"]))
    candidates.append(repo_root() / ".lake" / "packages")
    try:  # the main worktree, when this checkout is a linked worktree
        main = git("worktree", "list", "--porcelain").splitlines()[0].split(" ", 1)[1]
        candidates.append(Path(main) / ".lake" / "packages")
    except (subprocess.CalledProcessError, IndexError):
        pass
    for c in candidates:
        if c.exists() and compiled_mathlib(c.resolve()):
            return c.resolve()
    raise HarnessError(
        "no packages directory with a compiled mathlib found (tried: "
        + ", ".join(str(c) for c in candidates)
        + "). Pass --packages or set CIRCUITEQ_PACKAGES. The harness will not let lake "
          "download or build mathlib.")


def check_manifest_revs(ws: Path, packages: Path) -> None:
    """Every pinned revision must already be checked out, or lake would fetch."""
    manifest = json.loads((ws / "lake-manifest.json").read_text())
    for pkg in manifest.get("packages", []):
        name, rev = pkg.get("name"), pkg.get("rev")
        if not rev:
            continue
        d = packages / name
        if not d.exists():
            raise HarnessError(f"package `{name}` is missing from {packages}")
        have = git("rev-parse", "HEAD", cwd=d)
        if have != rev:
            raise HarnessError(f"package `{name}` is at {have[:12]}, the manifest pins {rev[:12]}; "
                               "lake would fetch. Use a packages directory built for this "
                               "manifest.")


def assert_lake_safe(ws: Path) -> None:
    link = ws / ".lake" / "packages"
    if not link.exists() or not compiled_mathlib(link.resolve()):
        raise HarnessError(f"refusing to run lake in {ws}: `.lake/packages` has no compiled "
                           "mathlib")


def ps_snapshot() -> dict[int, tuple[int, int, str]]:
    """pid -> (ppid, rss in KB, command)."""
    out = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,comm="], capture_output=True, text=True)
    table = {}
    for line in out.stdout.splitlines():
        parts = line.split(None, 3)
        if len(parts) == 4 and parts[0].isdigit():
            table[int(parts[0])] = (int(parts[1]), int(parts[2]), parts[3])
    return table


def descendants(root: int, table: dict[int, tuple[int, int, str]]) -> set[int]:
    kids: dict[int, list[int]] = {}
    for pid, (ppid, _, _) in table.items():
        kids.setdefault(ppid, []).append(pid)
    seen, stack = set(), [root]
    while stack:
        for k in kids.get(stack.pop(), []):
            if k not in seen:
                seen.add(k)
                stack.append(k)
    return seen


class Watchdog(threading.Thread):
    """Kills any `lean` or `leanchecker` process under `root` whose resident memory passes
    the limit."""

    def __init__(self, root: int, limit_mb: int, log: Path, interval: float = 2.0):
        super().__init__(daemon=True)
        self.root, self.limit_kb, self.log, self.interval = root, limit_mb * 1024, log, interval
        self.kills: list[dict] = []
        self.peak_kb = 0
        self._halt = threading.Event()

    def run(self) -> None:
        while not self._halt.wait(self.interval):
            table = ps_snapshot()
            for pid in descendants(self.root, table):
                _, rss, comm = table[pid]
                if os.path.basename(comm) not in ("lean", "leanchecker"):
                    continue
                self.peak_kb = max(self.peak_kb, rss)
                if rss > self.limit_kb:
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        continue
                    event = {"time": now(), "pid": pid, "rss_mb": rss // 1024}
                    self.kills.append(event)
                    with self.log.open("a") as f:
                        f.write(json.dumps(event) + "\n")

    def stop(self) -> None:
        self._halt.set()


def kill_tree(proc: subprocess.Popen) -> None:
    """Stop a process started in its own session, and whatever it left behind."""
    left = descendants(proc.pid, ps_snapshot())
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(proc.pid, sig)
        except (ProcessLookupError, PermissionError):
            pass
        for pid in left:
            try:
                os.kill(pid, sig)
            except (ProcessLookupError, PermissionError):
                pass
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            continue
        if sig == signal.SIGTERM:
            time.sleep(1)


# Lake must never fetch or compile a dependency here. The guards above make that
# impossible in principle; this stops it within a line of output if they are wrong.
TRIPWIRE = re.compile(
    r"cloning https?://|updating repository|checking out revision|"
    r"\bBuil(?:t|ding)\s+(?:Mathlib|Batteries|Aesop|Qq|ProofWidgets|Plausible|ImportGraph|"
    r"LeanSearchClient|Cli)\b")


def run_guarded(argv: list[str], cwd: Path, log: Path, timeout_s: float, limit_mb: int,
                watch: bool = True, env: dict[str, str] | None = None) -> tuple[int | None, str]:
    """Run a lake command under the packages guard, the dependency tripwire, a timeout and
    the memory watchdog. Returns the exit code (`None` on timeout) and the combined output.
    Inside a run the outer harness already watches the whole process tree, so `watch` is
    off there."""
    assert_lake_safe(cwd)
    with log.open("a") as f:
        f.write(f"\n$ {' '.join(argv)}   [{now()}]\n")
    proc = subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, bufsize=1, start_new_session=True,
                            env={**os.environ, **(env or {})})
    lines: list[str] = []
    tripped: list[str] = []

    def reader() -> None:
        assert proc.stdout is not None
        for line in proc.stdout:
            lines.append(line)
            if TRIPWIRE.search(line):
                tripped.append(line.strip())
                kill_tree(proc)
                return

    pump = threading.Thread(target=reader, daemon=True)
    pump.start()
    dog = Watchdog(proc.pid, limit_mb, log.with_name("watchdog.log")) if watch else None
    if dog:
        dog.start()
    try:
        proc.wait(timeout=timeout_s)
        rc: int | None = proc.returncode
    except subprocess.TimeoutExpired:
        kill_tree(proc)
        rc = None
    finally:
        if dog:
            dog.stop()
    pump.join(timeout=10)
    out = "".join(lines)
    if rc is None:
        out += f"\n[harness] timed out after {timeout_s:.0f} s\n"
    if dog and dog.kills:
        out += f"\n[harness] a Lean process passed {limit_mb} MB and was killed\n"
    with log.open("a") as f:
        f.write(out)
    if tripped:
        raise HarnessError("lake started to fetch or build a dependency and was stopped: "
                           + tripped[0] + f"\n(see {log})")
    return rc, out


# --------------------------------------------------------------------------
# prepare: the warm base of a library commit
# --------------------------------------------------------------------------

def base_dir(commit: str) -> Path:
    return harness_home() / "bases" / commit[:12]


def cmd_prepare(args) -> None:
    commit = git("rev-parse", args.commit)
    base = base_dir(commit)
    marker = base / ".harness-base.json"
    if marker.exists() and not args.force:
        print(f"base for {commit[:12]} is ready: {base}")
        return
    packages = find_packages(args.packages)
    if base.exists():
        shutil.rmtree(base)
    base.mkdir(parents=True)
    tar = subprocess.Popen(["git", "archive", "--format=tar", commit], cwd=repo_root(),
                           stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "-C", str(base)], stdin=tar.stdout, check=True)
    if tar.wait() != 0:
        raise HarnessError("git archive failed")
    check_manifest_revs(base, packages)
    (base / ".lake").mkdir()
    (base / ".lake" / "packages").symlink_to(packages)
    log = base / ".harness-prepare.log"
    print(f"building the library at {commit[:12]} in {base} (minutes; log: {log})")
    t0 = time.time()
    rc, out = run_guarded(["lake", "build"], base, log, args.timeout_min * 60,
                          args.memory_gb * 1024)
    if rc != 0:
        raise HarnessError(f"`lake build` failed in the base (exit {rc}); see {log}\n"
                           + out[-2000:])
    cold = time.time() - t0
    t0 = time.time()
    rc, _ = run_guarded(["lake", "build"], base, log, 600, args.memory_gb * 1024)
    warm = time.time() - t0
    if rc != 0:
        raise HarnessError(f"the second `lake build` failed; see {log}")
    marker.write_text(json.dumps({"commit": commit, "packages": str(packages), "built": now(),
                                  "cold_build_s": round(cold), "warm_build_s": round(warm)},
                                 indent=2))
    print(f"ready: cold build {cold:.0f} s, warm rebuild {warm:.0f} s")


# --------------------------------------------------------------------------
# setup: a run workspace
# --------------------------------------------------------------------------

def clone_tree(src: Path, dst: Path) -> None:
    """Copy a directory tree; on APFS a copy-on-write clone, so a base costs no disk."""
    if sys.platform == "darwin":
        if subprocess.run(["cp", "-Rcp", str(src), str(dst)]).returncode == 0:
            return
        shutil.rmtree(dst, ignore_errors=True)
    shutil.copytree(src, dst, symlinks=True)


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def drop_module(ws: Path, module: str) -> None:
    """Delete a module's source, its import in the umbrella and its build products."""
    rel = module_path(module)
    (ws / rel).unlink(missing_ok=True)
    umbrella = ws / "CircuitEq.lean"
    lines = [ln for ln in umbrella.read_text().splitlines() if ln.strip() != f"import {module}"]
    umbrella.write_text("\n".join(lines) + "\n")
    build = ws / ".lake" / "build"
    if build.exists():
        stem = rel.with_suffix("")
        for p in build.rglob(stem.name + ".*"):
            if p.is_file() and p.relative_to(build).parts[-len(stem.parts):-1] == stem.parts[:-1]:
                p.unlink()


def apply_redactions(ws: Path, redactions, notes: list[str]) -> None:
    for r in redactions:
        path = ws / r["file"]
        if not path.exists():
            notes.append(f"redaction skipped, no such file: {r['file']}")
            continue
        flags = 0
        for ch in r.get("flags", ""):
            flags |= {"m": re.M, "s": re.S, "i": re.I}[ch]
        text, count = re.subn(r["pattern"], r["replacement"], path.read_text(), flags=flags)
        if count == 0:
            notes.append(f"redaction did not match, the text may have moved: {r['file']}")
        path.write_text(text)


def strip_to_core(ws: Path) -> None:
    """The `core` configuration: the semantics, and none of the infrastructure."""
    lib = ws / "CircuitEq"
    for p in sorted(lib.rglob("*.lean")):
        module = ".".join(p.relative_to(ws).with_suffix("").parts)
        if module.split(".", 1)[1] not in CORE_MODULES:
            drop_module(ws, module)
    for d in sorted((p for p in lib.rglob("*") if p.is_dir()), reverse=True):
        if not any(d.iterdir()):
            d.rmdir()
    # A library commit from before `Relations` and `Decide` were split out of `Semantics`
    # has fewer core modules; import the ones it has.
    present = [m for m in CORE_MODULES if (lib / f"{m}.lean").exists()]
    (ws / "CircuitEq.lean").write_text("".join(f"import CircuitEq.{m}\n" for m in present))
    shutil.rmtree(ws / "scripts", ignore_errors=True)


def build_manifest(ws: Path) -> dict[str, str]:
    manifest = {}
    for p in sorted(ws.rglob("*")):
        rel = p.relative_to(ws)
        if (any(rel.parts[:len(d)] == d for d in (Path(s).parts for s in MANIFEST_SKIP_DIRS))
                or str(rel) in MANIFEST_SKIP_FILES or "__pycache__" in rel.parts):
            continue
        if p.is_file() and not p.is_symlink():
            manifest[str(rel)] = hashlib.sha256(p.read_bytes()).hexdigest()
    return manifest


def find_python_env(explicit: str | None) -> Path | None:
    """A virtual environment whose Python has numpy and pyzx (`scripts/tcount_survey.py`
    imports both), or `None`: `--python-env`, else `CIRCUITEQ_HARNESS_PYENV`, else `envs/pyzx`
    under the harness home, next to TZAP's. The system Python of this machine has neither."""
    for c in (explicit, os.environ.get("CIRCUITEQ_HARNESS_PYENV"),
              harness_home() / "envs" / "pyzx"):
        if c and (Path(c) / "bin" / "python").exists():
            ok = subprocess.run([str(Path(c) / "bin" / "python"), "-c", "import numpy, pyzx"],
                                capture_output=True)
            if ok.returncode == 0:
                return Path(c)
    return None


_TZAP: list = []


def find_tzap() -> tuple[Path | None, str | None]:
    """The TZAP command and its version, or `(None, None)`: `CIRCUITEQ_HARNESS_TZAP`, else the
    virtualenv `envs/tzap` under the harness home (see `benchmarks/harness/notes/README.md`
    for how it was installed). Checked by running `--version` once per process."""
    if not _TZAP:
        found = (None, None)
        for c in (os.environ.get("CIRCUITEQ_HARNESS_TZAP"),
                  str(harness_home() / "envs" / "tzap" / "bin" / "tzap")):
            if c and Path(c).is_file():
                try:
                    ok = subprocess.run([c, "--version"], capture_output=True, text=True,
                                        timeout=30)
                except (OSError, subprocess.TimeoutExpired):
                    continue
                if ok.returncode == 0:
                    found = (Path(c), ((ok.stdout or ok.stderr).split() or ["?"])[-1])
                    break
        _TZAP.append(found)
    return _TZAP[0]


def render_prompt(task: dict, budget_min: int, memory_gb: int, subagents: bool,
                  python_env: Path | None = None, prompt_file: str = "PROMPT.md",
                  extra: tuple[tuple[str, str], ...] = ()) -> str:
    """The prompt of a run. `prompt_file` and `extra` (more slots) are for a harness built on
    this one, which has its own fixed prompt with the same marker and the same slots."""
    text = (harness_dir() / prompt_file).read_text()
    marker = "<!-- prompt begins -->"
    if marker not in text:
        raise HarnessError(f"{prompt_file} has no `<!-- prompt begins -->` marker")
    text = text.split(marker, 1)[1].strip() + "\n"
    sub = ""
    if subagents:
        sub = ("\nYou may delegate sub-problems to subagents. They share this directory, your "
               "budget, the memory limit and the one-lake-at-a-time rule, and you remain "
               "responsible for what `./submit` sees.\n")
    py = ""
    if python_env is not None:
        py = ("- `./python` runs a Python that has `numpy` and `pyzx`; the plain `python3` of this "
              "machine has neither.\n")
    py += ("- `./qasm` converts between the Lean circuit lists here and OpenQASM 2, exactly "
           "(`./qasm --help`).\n")
    if find_tzap()[0] is not None:
        py += ("- `./tzap in.qasm -o out.qasm` runs the TZAP circuit optimiser (levels `-O1` to "
               "`-O3` and `-Osuper`; pass `--decompose-rz --decompose-cz` to get plain Clifford+T "
               "gates back). It is an untrusted oracle: what it returns proves nothing, and it may "
               "equal its input only up to a global phase.\n")
    for key, value in (("{relation_clause}", RELATIONS[task["relation"]][2]),
                       ("{python_clause}", py),
                       ("{budget_minutes}", str(budget_min)),
                       ("{memory_limit_gb}", str(memory_gb)),
                       ("{subagent_clause}", sub)) + tuple(extra):
        text = text.replace(key, value)
    return text


def playbook_for(base: Path, config: str) -> tuple[str, str]:
    """The prover's guide and where it came from. It is versioned with the library, so the
    base's copy wins; a commit older than the playbook falls back to this checkout's."""
    if config == "core":
        return (harness_dir() / "PLAYBOOK.core.md").read_text(), "harness (core)"
    for where, path in (("library commit", base / "PLAYBOOK.md"),
                        ("harness checkout", repo_root() / "PLAYBOOK.md")):
        if path.exists():
            return path.read_text(), where
    raise HarnessError("no PLAYBOOK.md in the library commit or in this checkout")


def new_run_id() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y%m%d-%H%M%S") + "-" + uuid.uuid4().hex[:6]


def setup_run(args, task: dict, customise=None) -> dict:
    """Make a run workspace: clone the base, hold the answer out, write the harness's files,
    build, and seal it with a manifest. `customise(ws, run)` is for a harness built on this
    one (`scripts/optimizer_harness.py`): it is called once the files below are written and
    before the workspace is built and hashed, and may replace them and add to `run`."""
    commit = git("rev-parse", args.commit)
    base = base_dir(commit)
    if not (base / ".harness-base.json").exists():
        raise HarnessError(f"no warm base for {commit[:12]}; "
                           f"run `prepare --commit {args.commit}` first")
    run_id = new_run_id()
    root = harness_home() / "runs" / run_id
    ws, meta = root / "ws", root / "meta"
    meta.mkdir(parents=True)
    playbook, playbook_source = playbook_for(base, args.config)
    clone_tree(base, ws)
    assert_lake_safe(ws)
    notes: list[str] = []

    for name in GLOBAL_DELETE + (".harness-base.json", ".harness-prepare.log", "watchdog.log"):
        p = ws / name
        if p.is_dir():
            shutil.rmtree(p)
        else:
            p.unlink(missing_ok=True)
    for module in task["holdout"].get("modules", []):
        drop_module(ws, module)
    for rel in task["holdout"].get("delete", []):
        p = ws / rel
        if p.is_dir():
            shutil.rmtree(p)
        else:
            p.unlink(missing_ok=True)
    if args.config == "core":
        strip_to_core(ws)
    else:
        apply_redactions(ws, GLOBAL_REDACT, notes)
        apply_redactions(ws, task["holdout"].get("redact", []), notes)

    sym = RELATIONS[task["relation"]][1]
    (ws / "Harness").mkdir()
    shutil.copyfile(Path(task["dir"]) / "Task.lean", ws / "Harness" / "Task.lean")
    (ws / "Harness.lean").write_text("import Harness.Task\n")
    (ws / "Solution.lean").write_text(SOLUTION_LEAN.replace("{sym}", sym))
    with (ws / "lakefile.toml").open("a") as f:
        f.write(LAKEFILE_PATCH)
    python_env = find_python_env(getattr(args, "python_env", None))
    if python_env is None:
        notes.append("no Python with numpy and pyzx found: the alignment script will not import")
    else:
        (ws / "python").write_text(
            PYTHON_SH.replace("{python}", str(python_env / "bin" / "python")))
        (ws / "python").chmod(0o755)
    tzap, tzap_version = find_tzap()
    if tzap is not None:
        (ws / "tzap").write_text(TZAP_SH.replace("{tzap}", str(tzap)))
        (ws / "tzap").chmod(0o755)
    shutil.copyfile(harness_dir() / "tools" / "qasm.py", ws / "qasm")
    (ws / "qasm").chmod(0o755)
    prompt = render_prompt(task, args.budget_min, args.memory_gb, args.subagents, python_env)
    (ws / "TASK.md").write_text(prompt)
    (ws / "CLAUDE.md").write_text(playbook)
    (ws / ".harness").mkdir()
    shutil.copyfile(SCRIPT, ws / ".harness" / "agent_harness.py")
    for name, body in (("submit", SUBMIT_SH), ("time-left", TIME_LEFT_SH)):
        (ws / name).write_text(body)
        (ws / name).chmod(0o755)

    run = {
        "run_id": run_id, "harness_version": HARNESS_VERSION, "library_commit": commit,
        "task": task["name"], "relation": task["relation"], "config": args.config,
        "subagents": bool(args.subagents), "budget_s": args.budget_min * 60,
        "memory_limit_mb": args.memory_gb * 1024, "playbook_source": playbook_source,
        "python_env": str(python_env) if python_env else None, "tzap": tzap_version,
        "instrument": instrument_hash(getattr(args, "agent", "claude")),
        "setup_notes": notes, "created": now(), "started": None, "deadline": None,
        "ws": str(ws), "meta": str(meta),
    }
    # What the agent can read says nothing about which task this is.
    in_run = {k: run[k] for k in ("relation", "budget_s", "memory_limit_mb", "started", "deadline")}
    (ws / ".harness" / "run.json").write_text(json.dumps(in_run, indent=2))
    if customise is not None:
        customise(ws, run)
        prompt = (ws / "TASK.md").read_text()

    log = meta / "setup.log"
    print(f"[{run_id}] warming the workspace (outside the clock; log: {log})")
    rc, out = run_guarded(["lake", "build", "CircuitEq", "Harness", "Solution"], ws, log,
                          args.setup_timeout_min * 60, args.memory_gb * 1024)
    if rc != 0:
        raise HarnessError(f"the workspace does not build (exit {rc}); see {log}\n" + out[-2000:])

    manifest = build_manifest(ws)
    (meta / "manifest.json").write_text(json.dumps(manifest, indent=1))
    (ws / ".harness" / "manifest.json").write_text(json.dumps(manifest, indent=1))
    shutil.copytree(ws, meta / "snapshot", symlinks=True,
                    ignore=shutil.ignore_patterns(".lake"))
    (meta / "prompt.md").write_text(prompt)
    (meta / "run.json").write_text(json.dumps(run, indent=2))
    for note in notes:
        print(f"[{run_id}] note: {note}")
    return run


def cmd_setup(args) -> None:
    run = setup_run(args, load_task(args.task))
    print(f"workspace: {run['ws']}\nprompt:    {run['meta']}/prompt.md\n"
          f"The clock is not running. Judge it later with: judge {run['run_id']}")


# --------------------------------------------------------------------------
# judge
# --------------------------------------------------------------------------

def changed_files(ws: Path, manifest: dict[str, str]) -> tuple[list[str], list[str], list[str]]:
    current = build_manifest(ws)
    modified = [p for p, h in manifest.items() if p in current and current[p] != h]
    deleted = [p for p in manifest if p not in current]
    added = [p for p in current if p not in manifest]
    return modified, deleted, added


def judge_workspace(ws: Path, relation: str, claims: list[str], manifest: dict[str, str],
                    log: Path, timeout_s: float, limit_mb: int, watch: bool) -> dict:
    """Judge a workspace for the first of `claims` that holds. The report says why not."""
    report = {"verdict": "REJECT", "claim": None, "axioms": None, "reasons": [], "warnings": [],
              "modified": [], "deleted": [], "added": [], "broke_rules": False}
    modified, deleted, added = changed_files(ws, manifest)
    report.update(modified=modified, deleted=deleted, added=added)
    protected = [p for p in modified + deleted if p not in EDITABLE]
    if protected:
        report["reasons"].append("files that existed at the start were changed or deleted: "
                                 + ", ".join(sorted(protected)))
    report["reasons"] += foreign_imports(ws, manifest)
    (ws / JUDGE_FILE).unlink(missing_ok=True)  # the judge writes its own, later
    for rel in sorted(set(added + modified)):
        if rel.endswith(".lean") and (ws / rel).exists():
            rejects, warns = scan_lean(ws / rel, rel)
            report["reasons"] += rejects
            report["warnings"] += warns
    if report["reasons"]:
        report["broke_rules"] = True
        return report

    rc, out = run_guarded(["lake", "build", "Solution"], ws, log, timeout_s, limit_mb, watch)
    if rc != 0:
        why = "timed out" if rc is None else f"exit {rc}"
        report["reasons"].append(f"`lake build Solution` failed ({why}):\n" + out[-3000:])
        return report

    name = "Quantum.Circuit.Harness.Judge.verdict"
    for claim in claims:
        (ws / JUDGE_FILE).write_text(
            JUDGE_LEAN.replace("{statement}", judge_statement(relation, claim))
            .replace("{claim}", claim))
        rc, out = run_guarded(["lake", "env", "lean", JUDGE_FILE], ws, log,
                              timeout_s, limit_mb, watch)
        axioms = parse_axioms(out, name)
        if rc != 0 or axioms is None:
            report["reasons"].append(f"`{claim}`: the restatement does not typecheck:\n"
                                     + out[-1500:])
            continue
        extra = [a for a in axioms if a not in ALLOWED_AXIOMS]
        if extra:
            report["reasons"].append(f"`{claim}` depends on {', '.join(extra)}; only "
                                     f"{', '.join(ALLOWED_AXIOMS)} are allowed")
            continue
        # The axiom report cannot see a declaration that never reached the kernel
        # (`debug.skipKernelTC`, or meta code that adds one unchecked). `leanchecker`, shipped
        # with the toolchain, replays every declaration of the agent's modules through the
        # kernel in a process where none of their options or meta code runs. One thread: each
        # extra thread loads its own copy of the mathlib imports.
        rc, out = run_guarded(["lake", "env", "leanchecker", "-v", "Solution"], ws, log,
                              timeout_s, limit_mb, watch, env={"LEAN_NUM_THREADS": "1"})
        if rc != 0:
            why = "timed out" if rc is None else f"exit {rc}"
            report["reasons"].append(f"`{claim}`: the kernel replay of the solution failed "
                                     f"({why}):\n" + out[-1500:])
            report["broke_rules"] = rc is not None and "(kernel)" in out
            return report
        report.update(verdict="ACCEPT", claim=claim, axioms=axioms, reasons=[], replayed=True)
        return report
    return report


def cmd_submit(args) -> None:
    """What `./submit` runs inside a workspace. Advisory: the run is scored from outside."""
    ws = Path(args.ws).resolve()
    run = json.loads((ws / ".harness" / "run.json").read_text())
    manifest = json.loads((ws / ".harness" / "manifest.json").read_text())
    if args.claim not in CLAIMS:
        sys.exit("usage: ./submit equiv   or   ./submit not_equiv")
    report = judge_workspace(ws, run["relation"], [args.claim], manifest,
                             ws / ".harness" / "submit.log", JUDGE_TIMEOUT_S,
                             run["memory_limit_mb"], watch=False)
    elapsed = None
    if run.get("started"):
        elapsed = round(time.time() - run["started"])
    with (ws / ".harness" / "submissions.jsonl").open("a") as f:
        f.write(json.dumps({"time": now(), "elapsed_s": elapsed, "claim": args.claim,
                            "verdict": report["verdict"]}) + "\n")
    if report["verdict"] == "ACCEPT":
        print(f"ACCEPT: `{args.claim}` is proved on the axioms {report['axioms']}. "
              "You are done; stop.")
    else:
        print("REJECT")
        for reason in report["reasons"]:
            print(" - " + reason)
    for w in report["warnings"]:
        print(f"note (a person will look at this): {w}")


def cmd_time_left(args) -> None:
    run = json.loads((Path(args.ws) / ".harness" / "run.json").read_text())
    if not run.get("deadline"):
        print(f"the clock is not running (budget {run['budget_s'] // 60} min)")
        return
    left = run["deadline"] - time.time()
    if left <= 0:
        print("0 min left: the deadline has passed")
    else:
        print(f"{int(left // 60)} min {int(left % 60)} s left of {run['budget_s'] // 60} min")


def resolve_run(ref: str) -> Path:
    p = Path(ref)
    root = p if p.exists() else harness_home() / "runs" / ref
    if not (root / "meta" / "run.json").exists():
        raise HarnessError(f"no run at {root}")
    return root


def final_judge(root: Path) -> dict:
    """The verdict of record: judged from outside, against the manifest the agent cannot reach."""
    meta, ws = root / "meta", root / "ws"
    run = json.loads((meta / "run.json").read_text())
    manifest = json.loads((meta / "manifest.json").read_text())
    claims = list(CLAIMS)
    submissions = read_submissions(ws)
    accepted = [s["claim"] for s in submissions if s["verdict"] == "ACCEPT"]
    if accepted and accepted[-1] in CLAIMS:
        claims.sort(key=lambda c: c != accepted[-1])
    report = judge_workspace(ws, run["relation"], claims, manifest, meta / "judge.log",
                             JUDGE_TIMEOUT_S, run["memory_limit_mb"], watch=True)
    report["submissions"] = submissions
    first = next((s for s in submissions if s["verdict"] == "ACCEPT"), None)
    accepted_run = first is not None and report["verdict"] == "ACCEPT"
    report["first_accept_s"] = first["elapsed_s"] if accepted_run else None
    write_changes_diff(meta / "snapshot", ws, meta / "changes.diff")
    (meta / "judge.json").write_text(json.dumps(report, indent=2, ensure_ascii=False))
    return report


def write_changes_diff(snapshot: Path, ws: Path, out: Path) -> None:
    """What a workspace changed since its start, for a person to read before trusting a row."""
    diff = subprocess.run(["diff", "-ruN", "--exclude=.lake", "--exclude=.harness",
                           "--exclude=__pycache__", "--exclude=Judge.lean", str(snapshot), str(ws)],
                          capture_output=True, text=True)
    out.write_text(diff.stdout.replace(str(Path.home()), "~"))  # these files are committed


def read_submissions(ws: Path) -> list[dict]:
    """What `./submit` appended to `submissions.jsonl`, skipping a line torn by the kill at
    the deadline (the agent's whole session is stopped while `./submit` may be writing)."""
    path = ws / ".harness" / "submissions.jsonl"
    if not path.exists():
        return []
    out = []
    for line in path.read_text().splitlines():
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return out


def outcome_of(report: dict) -> str:
    if report["verdict"] == "ACCEPT":
        return "proved" if report["claim"] == "equiv" else "refuted"
    return "invalid" if report.get("broke_rules") else "no_certificate"


def cmd_judge(args) -> None:
    root = resolve_run(args.run)
    report = final_judge(root)
    print_report(json.loads((root / "meta" / "run.json").read_text()), report, root)


def print_report(run: dict, report: dict, root: Path) -> None:
    print(f"\n[{run['run_id']}] {run['task']} / {run['config']}: {outcome_of(report)}")
    if report["verdict"] == "ACCEPT":
        when = report["first_accept_s"]
        print(f"  claim `{report['claim']}`, axioms {report['axioms']}, "
              + (f"first accepted after {when} s" if when is not None
                 else "never submitted by the agent"))
    for reason in report["reasons"]:
        print("  - " + reason.splitlines()[0])
    print(f"  added: {report['added'] or 'nothing'}")
    print(f"  modified: {report['modified'] or 'nothing'}; "
          f"deleted: {report['deleted'] or 'nothing'}")
    for w in report["warnings"]:
        print(f"  look at: {w}")
    print(f"  read the diff before trusting the verdict: {root / 'meta' / 'changes.diff'}")


# --------------------------------------------------------------------------
# run: setup, agent, judge, record
# --------------------------------------------------------------------------

def agent_argv(config: dict, prompt: str, model: str, subagents: bool,
               max_usd: float | None) -> list[str]:
    """The command line that runs the agent on `prompt`, from its configuration file."""
    disallowed = list(config.get("disallowed_tools", []))
    if not subagents:
        disallowed += config.get("subagent_tools", [])
    subst = {"{prompt}": prompt, "{model}": model,
             "{allowed_tools}": ",".join(config.get("allowed_tools", [])),
             "{builtin_tools}": ",".join(config.get("builtin_tools", [])
                                         + (config.get("subagent_tools", []) if subagents else [])),
             "{disallowed_tools}": ",".join(disallowed)}
    argv = [subst.get(a, a) for a in config["argv"]]
    if max_usd is not None and config.get("max_usd_flag"):
        argv += [config["max_usd_flag"], str(max_usd)]
    return argv


def tool_counts(transcript: Path) -> dict[str, int]:
    """How often the agent called each tool; the Lean language-server tools as `lsp:name`."""
    counts: dict[str, int] = {}
    for line in transcript.read_text(errors="replace").splitlines():
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if rec.get("type") == "assistant":
            for block in rec.get("message", {}).get("content", []):
                if block.get("type") == "tool_use":
                    name = block["name"].replace("mcp__lean-lsp__", "lsp:")
                    counts[name] = counts.get(name, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: -kv[1]))


def instrument_hash(agent: str, prompt_file: str = "PROMPT.md") -> str:
    """One hash over the prompt and the agent configuration, so two rows can be told apart."""
    h = hashlib.sha256((harness_dir() / prompt_file).read_bytes())
    config = harness_dir() / "agents" / f"{agent}.json"
    if config.exists():
        h.update(config.read_bytes())
    return h.hexdigest()[:12]


def agent_result(transcript: Path) -> dict:
    """Cost, turns and token use, if the agent's output ends with a result record."""
    result = {}
    for line in transcript.read_text(errors="replace").splitlines():
        if line.startswith("{"):
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            if rec.get("type") == "result":
                result = {k: rec.get(k)
                          for k in ("total_cost_usd", "num_turns", "duration_ms",
                                    "duration_api_ms", "usage", "is_error", "subtype")}
    return result


def agent_config(agent: str) -> dict:
    """The launch configuration under `agents/`; `none` runs the pipeline without an agent."""
    if agent == "none":
        return {}
    return json.loads((harness_dir() / "agents" / f"{agent}.json").read_text())


def run_agent(args, run: dict, config: dict, model: str) -> tuple[bool, float, Watchdog]:
    """Start the clock and the agent in a prepared workspace, watch its memory, and stop it
    at the budget plus the grace. Returns whether the deadline stopped it, its wall time and
    the watchdog. Shared by every harness built on this workspace."""
    ws, meta = Path(run["ws"]), Path(run["meta"])
    timed_out = False
    argv = agent_argv(config, (meta / "prompt.md").read_text(), model, args.subagents, args.max_usd)
    start = time.time()
    run.update(started=start, deadline=start + run["budget_s"])
    in_run = json.loads((ws / ".harness" / "run.json").read_text())
    in_run.update(started=start, deadline=run["deadline"])
    (ws / ".harness" / "run.json").write_text(json.dumps(in_run, indent=2))
    (meta / "run.json").write_text(json.dumps(run, indent=2))
    print(f"[{run['run_id']}] agent `{args.agent}` ({model}), {args.budget_min} min, "
          f"{args.memory_gb} GB per Lean process")
    def ignore_sigterm(*_) -> None:
        with (meta / "harness-signals.log").open("a") as f:
            f.write(f"{now()} SIGTERM ignored while the agent runs\n")

    signal.signal(signal.SIGTERM, ignore_sigterm)
    with (meta / "transcript.jsonl").open("w") as out:
        proc = subprocess.Popen(argv, cwd=ws, stdin=subprocess.DEVNULL, stdout=out,
                                stderr=subprocess.STDOUT, start_new_session=True)
        dog = Watchdog(proc.pid, run["memory_limit_mb"], meta / "watchdog.log")
        dog.start()
        try:
            proc.wait(timeout=run["budget_s"] + args.grace_s)
        except subprocess.TimeoutExpired:
            timed_out = True
        finally:
            kill_tree(proc)  # also reaps the language server the agent started
            dog.stop()
            signal.signal(signal.SIGTERM, signal.SIG_DFL)
    return timed_out, time.time() - start, dog


def cmd_run(args) -> None:
    task = load_task(args.task)
    config = agent_config(args.agent)
    model = args.model or config.get("default_model", "")
    run = setup_run(args, task)
    root, meta = Path(run["ws"]).parent, Path(run["meta"])
    run.update(agent=args.agent, model=model, run_index=args.run_index)

    timed_out, agent_wall, dog = False, 0.0, None
    if args.agent != "none":
        timed_out, agent_wall, dog = run_agent(args, run, config, model)

    (meta / "run.json").write_text(json.dumps(run, indent=2))
    record_run(root, timed_out=timed_out, agent_wall=agent_wall, dog=dog, note=args.note)


def result_row(root: Path, run: dict, report: dict, fields: dict, timed_out: bool = False,
               agent_wall: float | None = None, dog: "Watchdog | None" = None,
               note: str = "") -> dict:
    """One row of a results file. What produced the result (harness, library, model,
    instrument, budget, environment, what the agent called) is recorded the same way by
    every harness built on this workspace; `fields` are the harness's own, after the date.
    `report` is a judge's: its submissions, file changes, warnings and reasons."""
    transcript = root / "meta" / "transcript.jsonl"
    has_agent = run.get("agent", "none") != "none" and transcript.exists()
    if agent_wall is None and has_agent and run.get("started"):
        agent_wall = transcript.stat().st_mtime - run["started"]  # the harness did not see the end
    return {
        **{k: run.get(k) for k in ("run_id", "harness_version", "library_commit", "task", "config",
                                   "subagents", "agent", "model", "run_index", "budget_s",
                                   "memory_limit_mb", "playbook_source", "python_env", "tzap",
                                   "setup_notes")},
        "date": now(), **fields, "agent_wall_s": round(agent_wall or 0),
        "timed_out": timed_out, "submissions": len(report["submissions"]),
        "watchdog_kills": len(dog.kills) if dog else None,
        "peak_lean_mb": (dog.peak_kb // 1024) if dog else None,
        "added": report["added"], "modified": report["modified"], "deleted": report["deleted"],
        "warnings": report["warnings"], "reasons": [r.splitlines()[0] for r in report["reasons"]],
        "agent_result": agent_result(transcript) if has_agent else {},
        "tool_calls": tool_counts(transcript) if has_agent else {},
        "instrument": run.get("instrument") or instrument_hash(run.get("agent", "none")),
        "note": note, "reviewed": False,
        "run_dir": str(root).replace(str(Path.home()), "~"),  # the row is committed
    }


def record_run(root: Path, timed_out: bool = False, agent_wall: float | None = None,
               dog: "Watchdog | None" = None, note: str = "") -> None:
    """Judge a run from outside, append its row to `results.jsonl` and keep its solution."""
    ws, meta = root / "ws", root / "meta"
    run = json.loads((meta / "run.json").read_text())
    task = load_task(run["task"])
    report = final_judge(root)
    row = result_row(root, run, report, {
        "expected": task.get("expected"), "outcome": outcome_of(report), "claim": report["claim"],
        "axioms": report["axioms"], "first_accept_s": report["first_accept_s"],
    }, timed_out, agent_wall, dog, note)
    results = harness_dir() / "results"
    results.mkdir(exist_ok=True)
    with (results / "results.jsonl").open("a") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")
    keep = results / run["run_id"]
    keep.mkdir(exist_ok=True)
    for rel in ["Solution.lean"] + [a for a in report["added"] if a.endswith(".lean")]:
        if (ws / rel).exists():
            (keep / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ws / rel, keep / rel)
    for name in ("changes.diff", "judge.json"):
        shutil.copyfile(meta / name, keep / name)
    print_report(run, report, root)
    print(f"  recorded in {results / 'results.jsonl'} "
          '(set "reviewed" once you have read the diff)')


def cmd_record(args) -> None:
    """For a run whose harness process died before judging: judge it and write its row."""
    record_run(resolve_run(args.run), note=args.note)


def cmd_digest(args) -> None:
    """What the agent said and did, one line per step, from a run's transcript."""
    path = resolve_run(args.run) / "meta" / "transcript.jsonl"
    for line in path.read_text(errors="replace").splitlines():
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if rec.get("type") == "assistant":
            for block in rec.get("message", {}).get("content", []):
                if block.get("type") == "text" and block["text"].strip():
                    print("says |", " ".join(block["text"].split())[:args.width])
                elif block.get("type") == "tool_use":
                    inp = block.get("input", {})
                    arg = (inp.get("command") or inp.get("file_path") or inp.get("pattern")
                           or inp.get("query") or json.dumps(inp))
                    name = block["name"].replace("mcp__lean-lsp__", "lsp:")
                    print(f"{name:5}|", " ".join(str(arg).split())[:args.width])
        elif rec.get("type") == "result":
            print("\nresult:", {k: rec.get(k) for k in ("subtype", "num_turns", "total_cost_usd",
                                                         "duration_ms")})
    print("tool calls:", tool_counts(path))


# --------------------------------------------------------------------------
# selftest: everything that needs neither lake nor an agent
# --------------------------------------------------------------------------

def cmd_selftest(_args) -> None:
    assert fmt_lean_list([]) == "[]"
    gates = [f"CX {i} {i + 1}" for i in range(40)]
    text = fmt_lean_list(gates)
    assert all(len(ln) <= 96 for ln in text.splitlines()) and text.count("CX") == 40
    assert [" ".join(g.split()) for g in text.strip("[]").replace("\n", " ").split(",")] == gates

    src = ("theorem a : True := by\n  trivial -- native_decide would be wrong\n"
           "/- debug.skipKernelTC /- nested -/ -/\n")
    stripped = strip_lean_comments(src)
    assert "native_decide" not in stripped and "debug" not in stripped
    name = "Quantum.Circuit.Harness.Judge.verdict"
    axioms_out = f"'{name}' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
    assert parse_axioms(axioms_out, name) == ["propext", "Classical.choice", "Quot.sound"]
    assert parse_axioms(f"'{name}' does not depend on any axioms", name) == []
    assert parse_axioms("error: unknown constant", name) is None
    assert judge_statement("u", "not_equiv").startswith("¬ Quantum.Circuit.Equivalent ")

    with tempfile.TemporaryDirectory() as tmp:
        ws = Path(tmp) / "ws"
        (ws / "CircuitEq" / "Benchmarks").mkdir(parents=True)
        (ws / ".lake" / "build" / "lib" / "lean" / "CircuitEq" / "Benchmarks").mkdir(parents=True)
        (ws / "CircuitEq.lean").write_text(
            "import CircuitEq.Semantics\nimport CircuitEq.Benchmarks.Tof3\n")
        (ws / "CircuitEq" / "Semantics.lean").write_text("-- semantics\n")
        (ws / "CircuitEq" / "Benchmarks" / "Tof3.lean").write_text("-- answer\n")
        olean = ws / ".lake" / "build" / "lib" / "lean" / "CircuitEq" / "Benchmarks" / "Tof3.olean"
        olean.write_text("x")
        other = ws / ".lake" / "build" / "lib" / "lean" / "CircuitEq" / "Tof3.olean"
        other.write_text("x")
        drop_module(ws, "CircuitEq.Benchmarks.Tof3")
        assert not olean.exists() and other.exists(), "only the held-out module's products go"
        assert "Tof3" not in (ws / "CircuitEq.lean").read_text()

        (ws / "Solution.lean").write_text("theorem equiv : True := by\n  sorry\n")
        manifest = build_manifest(ws)
        assert ".lake" not in " ".join(manifest)
        (ws / "Solution.lean").write_text("theorem equiv : True := trivial\n")
        (ws / "CircuitEq" / "Semantics.lean").write_text("-- edited\n")
        (ws / "Solution").mkdir()
        (ws / "Solution" / "Lemmas.lean").write_text("set_option debug.skipKernelTC true\n")
        modified, deleted, added = changed_files(ws, manifest)
        assert sorted(modified) == ["CircuitEq/Semantics.lean", "Solution.lean"] and not deleted
        assert added == ["Solution/Lemmas.lean"]
        report = judge_workspace(ws, "u", ["equiv"], manifest, ws / "log", 1, 1, watch=False)
        assert report["verdict"] == "REJECT" and len(report["reasons"]) == 2, report
        assert "CircuitEq/Semantics.lean" in report["reasons"][0]
        assert "debug" in report["reasons"][1]

        notes: list[str] = []
        (ws / "scripts").mkdir()
        (ws / "scripts" / "certificate.py").write_text(
            "A = 1\nBENCHMARKS = {\n  'x': 1,\n}\nB = 2\n")
        apply_redactions(ws, GLOBAL_REDACT, notes)
        assert (ws / "scripts" / "certificate.py").read_text() == "A = 1\nBENCHMARKS = {}\nB = 2\n"
        apply_redactions(ws, GLOBAL_REDACT, notes)
        assert len(notes) == 1 and "did not match" in notes[0]
        try:
            assert_lake_safe(ws)
            raise AssertionError("lake must be refused without a compiled mathlib")
        except HarnessError:
            pass

    for d in task_dirs():
        task = load_task(d.name)
        body = (d / "Task.lean").read_text()
        for which in ("original", "optimized"):
            m = re.search(rf"def {which} : Circuit (\d+) :=\s*\[([^\]]*)\]", body)
            assert m and int(m[1]) == task["qubits"], f"{d.name}: {which}"
        render_prompt(task, 30, 6, False)
    print("selftest passed")


# --------------------------------------------------------------------------

def add_run_options(p: argparse.ArgumentParser) -> None:
    p.add_argument("task")
    p.add_argument("--commit", default="HEAD", help="library commit (must have been prepared)")
    p.add_argument("--config", choices=("full", "core"), default="full",
                   help="`core` strips the library to the semantics and its decision procedures")
    p.add_argument("--budget-min", type=int, default=30)
    p.add_argument("--memory-gb", type=int, default=6, help="limit per Lean process")
    p.add_argument("--setup-timeout-min", type=int, default=30)
    p.add_argument("--subagents", action="store_true", help="leave the subagent tool enabled")
    p.add_argument("--python-env", help="a virtualenv with numpy and pyzx, offered as ./python")


def add_agent_options(p: argparse.ArgumentParser) -> None:
    p.add_argument("--agent", default="claude",
                   help="a file under benchmarks/harness/agents, or `none`")
    p.add_argument("--model")
    p.add_argument("--run-index", type=int, default=0)
    p.add_argument("--max-usd", type=float)
    p.add_argument("--grace-s", type=int, default=30, help="time past the budget before the kill")
    p.add_argument("--note", default="", help="recorded with the result, e.g. machine conditions")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("tasks").set_defaults(fn=cmd_tasks)
    sub.add_parser("selftest").set_defaults(fn=cmd_selftest)

    p = sub.add_parser("import-benchmark")
    p.add_argument("module", help="module name under CircuitEq/Benchmarks, e.g. Tof3")
    p.add_argument("--name", required=True)
    p.add_argument("--relation", choices=tuple(RELATIONS), default="u")
    p.add_argument("--mutant", type=int, help="seed: delete one gate of `optimized`")
    p.add_argument("--family")
    p.add_argument("--rung", type=int)
    p.add_argument("--pipeline")
    p.set_defaults(fn=cmd_import_benchmark)

    p = sub.add_parser("import-pair")
    p.add_argument("file", help="JSON: name, qubits, original, optimized (gate strings)")
    p.set_defaults(fn=cmd_import_pair)

    p = sub.add_parser("prepare")
    p.add_argument("--commit", default="HEAD")
    p.add_argument("--packages", help="a `.lake/packages` with a compiled mathlib")
    p.add_argument("--force", action="store_true")
    p.add_argument("--timeout-min", type=int, default=90)
    p.add_argument("--memory-gb", type=int, default=8)
    p.set_defaults(fn=cmd_prepare)

    p = sub.add_parser("setup")
    add_run_options(p)
    p.set_defaults(fn=cmd_setup)

    p = sub.add_parser("run")
    add_run_options(p)
    add_agent_options(p)
    p.set_defaults(fn=cmd_run)

    p = sub.add_parser("judge")
    p.add_argument("run", help="a run id, or the path of a run directory")
    p.set_defaults(fn=cmd_judge)

    p = sub.add_parser("record")
    p.add_argument("run", help="a run id, or the path of a run directory")
    p.add_argument("--note", default="")
    p.set_defaults(fn=cmd_record)

    p = sub.add_parser("digest")
    p.add_argument("run", help="a run id, or the path of a run directory")
    p.add_argument("--width", type=int, default=200)
    p.set_defaults(fn=cmd_digest)

    for name, fn in (("submit", cmd_submit), ("time-left", cmd_time_left)):
        p = sub.add_parser(name)
        p.add_argument("--ws", required=True)
        if name == "submit":
            p.add_argument("claim", nargs="?", default="")
        p.set_defaults(fn=fn)

    args = parser.parse_args()
    try:
        args.fn(args)
    except HarnessError as e:
        sys.exit(f"harness: {e}")


if __name__ == "__main__":
    main()
