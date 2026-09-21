#!/usr/bin/env python3
"""Agent harness for the optimisation task (draft).

A task is one Clifford+T circuit, `original`, and a cost function. The harness
gives an agent a warm copy of the library, one fixed prompt, a wall-clock
budget and a memory limit, and asks for a cheaper circuit `optimized` together
with a Lean proof that the two are equivalent. The Lean kernel guarantees the
equivalence; only the quality of the result depends on the agent. External
optimisers are untrusted oracles: the agent may call them, but only what it
proves is scored.

This script is the sibling of `scripts/agent_harness.py` (the equivalence-checking
task) and imports it for everything the two share: the warm bases and `prepare`,
the lake guards and the dependency tripwire, the memory watchdog, workspace
setup and hold-out, the manifest and the protected-files check, the forbidden-text
scan, the judge of `equiv` (restatement, axioms, kernel replay), the agent launch
with its deadline and signal handling, `./time-left`, `./python`, `digest`, and
the attribution fields of a result row. What is here is what differs: the task
format, the stub, the cost, the snapshots of accepted submissions, and the score.

Commands (build a base with `agent_harness.py prepare`, read a transcript with
`agent_harness.py digest`; runs of both harnesses live side by side):

    tasks                         list the optimisation tasks
    import-pair FILE              make a task from the `original` of a pair JSON file
    import-benchmark MODULE       ... from `CircuitEq/Benchmarks/MODULE.lean`
    import-task NAME              ... from a task of the equivalence harness
    baseline TASK TOOL            record what an external tool reaches on a task
    setup TASK                    make a run workspace and stop (inspect it, or run by hand)
    run TASK                      setup, agent, judge, record
    judge RUN                     judge a finished run again
    record RUN                    judge and record a run whose harness process died
    selftest                      check the parts that need neither lake nor an agent

Inside a run workspace the agent sees `./submit` (the judge) and `./time-left`.

The judge: the equivalence harness's check that `equiv` proves exactly
`original ≡ᵤ optimized` about the harness's `original` and the agent's
`optimized`, on the three standard axioms, with the agent's modules replayed
through the kernel; then the cost of `optimized`, which the harness measures
and the agent never claims. The harness owns `Harness/Cost.lean`; the judge
evaluates its functions on the agent's constant with `#eval` and has the kernel
confirm the numbers by `decide +kernel`. The constant measured is the constant
the theorem is about, so the proof covers the cost.

Anytime and monotone: every accepted submission is copied under
`.harness/accepted/<k>/`, the score is the cheapest of them, and the working
files may be in any state at the deadline. The verdict of record re-judges the
cheapest copy in a fresh clone of the workspace as it was before the agent
started, so nothing the agent left in the build directory or outside
`Solution.lean` and `Solution/` can reach it, and falls back to the next
cheapest if that fails. A run never fails: with no certified improvement its
score is the cost of `original`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_harness as ah  # noqa: E402  (in a run workspace: the copy beside this file)
from agent_harness import HarnessError  # noqa: E402

OPT_HARNESS_VERSION = "0.2-draft"

SCRIPT = Path(__file__).resolve()
PROMPT_FILE = "PROMPT.optimize.md"
RESULTS_FILE = "opt-results.jsonl"

# The cost functions of `Harness/Cost.lean`, in the order `Cost.measure` lists them: key ->
# (name in the prompt, definition in words, the gates it counts or `None` for all of them).
COSTS = {
    "tCount": ("T-count", "the number of `T` and `Tdg` gates", ("T", "Tdg")),
    "cxCount": ("CNOT count", "the number of `CX` gates", ("CX",)),
    "gateCount": ("gate count", "the number of gates of any kind", None),
}
# T gates dominate a fault-tolerant cost, two-qubit gates come next, and the total keeps an
# optimiser from ignoring size altogether (decided 19 September 2026).
DEFAULT_COST_ORDER = ("tCount", "cxCount", "gateCount")

# Where `./submit` keeps a copy of every accepted submission, and the judge's scratch module
# (a solution may not import it): named by the equivalence harness, whose manifest skips both.
ACCEPTED = Path(ah.ACCEPTED_DIR)
JUDGE_FILE = ah.JUDGE_FILE
COST_THEOREM = "Quantum.Circuit.Harness.Judge.cost"
MEASURE_RE = re.compile(r"^\[(\d+), (\d+), (\d+)\]\s*$", re.M)

# The stub's proof of `equiv`, per relation: it must typecheck against `optimized := original`.
STUB_PROOFS = {
    "u": "Equivalent.refl _",
    "p": "(Equivalent.refl _).toUpToPhase",
    "s": "(Equivalent.refl _).toUpToScalar",
}

TASK_LEAN = """\
import CircuitEq.Semantics

/-! # The task

The circuit of this run. The harness owns this file: a run that edits it is
rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The circuit to optimise. -/
def original : Circuit {n} :=
  {original}

end Quantum.Circuit.Harness
"""

COST_LEAN = """\
import CircuitEq.Semantics

/-! # What a circuit costs

The harness's definition, not the library's, which has no cost functions yet.
The harness owns this file: a run that edits it is rejected. The judge
evaluates these functions on the solution's `optimized` and has the kernel
confirm the numbers, so a cost is measured, never claimed.
-/

namespace Quantum.Circuit.Harness.Cost

/-- T-count: the number of `T` and `T†` gates. -/
def tCount {n : ℕ} (c : Circuit n) : ℕ :=
  c.countP fun g => match g with
    | .one .T _ | .one .Tdg _ => true
    | _ => false

/-- CNOT count: the number of `CX` gates. -/
def cxCount {n : ℕ} (c : Circuit n) : ℕ :=
  c.countP fun g => match g with
    | .cnot _ _ => true
    | _ => false

/-- Gate count: the number of gates of any kind. -/
def gateCount {n : ℕ} (c : Circuit n) : ℕ :=
  c.length

/-- The three costs in the order the judge reads them. -/
def measure {n : ℕ} (c : Circuit n) : List ℕ :=
  [tCount c, cxCount c, gateCount c]

end Quantum.Circuit.Harness.Cost
"""

SOLUTION_LEAN = """\
import CircuitEq
import Harness.Task

/-! # Solution

Replace `optimized` by a cheaper circuit and keep `equiv` proved. Then run
`./submit`. As it stands this file is accepted, at the cost of `original`.

Lemmas may go in this file, and new modules under `Solution/` (import them
here). No other existing file may be edited.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The cheaper circuit. -/
def optimized : Circuit {n} :=
  original

/-- It does what `original` does. -/
theorem equiv : original {sym} optimized :=
  {proof}

end Quantum.Circuit.Harness
"""

MEASURE_LEAN = """\
{imports}

/-! Written by the harness when it judges: the cost of `{circuit}` by the harness's own cost
functions. This evaluation only finds the numbers; the kernel confirms them next. -/

#eval Quantum.Circuit.Harness.Cost.measure Quantum.Circuit.Harness.{circuit}
"""

CONFIRM_LEAN = """\
{imports}

/-! Written by the harness when it judges: the measured cost of `{circuit}`, stated with fully
qualified names and checked by the kernel, which evaluates a list and three numbers. -/

theorem Quantum.Circuit.Harness.Judge.cost :
    Quantum.Circuit.Harness.Cost.tCount Quantum.Circuit.Harness.{circuit} = {tCount} ∧
    Quantum.Circuit.Harness.Cost.cxCount Quantum.Circuit.Harness.{circuit} = {cxCount} ∧
    Quantum.Circuit.Harness.Cost.gateCount Quantum.Circuit.Harness.{circuit} = {gateCount} := by
  decide +kernel

#print axioms Quantum.Circuit.Harness.Judge.cost
"""

SUBMIT_SH = """\
#!/bin/sh
# The judge. Usage: ./submit
here="$(cd "$(dirname "$0")" && pwd)"
exec python3 "$here/.harness/optimizer_harness.py" submit --ws "$here" "$@"
"""


# --------------------------------------------------------------------------
# Cost
# --------------------------------------------------------------------------

def python_cost(gates: list[str]) -> dict[str, int]:
    """The cost of a gate list, counted here. For `task.json` and baselines only: the cost
    of a submission is always measured in Lean."""
    names = [g.split()[0] for g in gates]
    return {key: len(names) if kinds is None else sum(name in kinds for name in names)
            for key, (_, _, kinds) in COSTS.items()}


def score(cost: dict, order) -> list[int]:
    """The entries of a cost that a task compares, in its order; lists compare
    lexicographically, which is the order of the score."""
    out = [cost[key] for key in order]
    if not all(isinstance(v, int) and not isinstance(v, bool) and v >= 0 for v in out):
        raise ValueError(f"not a cost: {cost!r}")
    return out


def check_cost_order(order, where: str) -> list[str]:
    order = list(order)
    if not order or len(set(order)) != len(order) or any(key not in COSTS for key in order):
        raise HarnessError(f"{where}: `cost_order` must be distinct names among {list(COSTS)}")
    return order


def cost_words(cost: dict, order) -> str:
    """`T-count 21, gate count 45 (CNOT count 18)`: the compared entries, then the rest."""
    text = ", ".join(f"{COSTS[key][0]} {cost[key]}" for key in order)
    rest = ", ".join(f"{COSTS[key][0]} {cost[key]}" for key in COSTS if key not in order)
    return text + (f" ({rest})" if rest else "")


def cost_clause(order) -> str:
    """The cost function of a task, stated exactly, for the prompt."""
    names = [COSTS[key][0] for key in order]
    defs = "; ".join(f"{COSTS[key][0]} (`{key}`) is {COSTS[key][1]}" for key in order)
    if len(order) == 1:
        return f"The cost of a circuit is its {names[0]}, and lower is better: {defs}."
    if len(order) == 2:
        how = (f"a lower {names[0]} is better, and the {names[1]} only breaks ties between "
               f"circuits of equal {names[0]}")
    else:
        how = (f"a lower {names[0]} is better, and each later entry only breaks ties between "
               "circuits that agree on all the entries before it")
    return (f"The cost of a circuit is the {'pair' if len(order) == 2 else 'tuple'} "
            f"({', '.join(names)}), compared lexicographically: {how}. Here {defs}.")


# --------------------------------------------------------------------------
# Tasks
# --------------------------------------------------------------------------

def tasks_dir() -> Path:
    return ah.harness_dir() / "opt-tasks"


def task_dirs() -> list[Path]:
    if not tasks_dir().exists():
        return []
    return sorted(p for p in tasks_dir().iterdir() if (p / "task.json").exists())


def load_task(name: str) -> dict:
    path = tasks_dir() / name / "task.json"
    if not path.exists():
        raise HarnessError(f"no optimisation task `{name}` (looked for {path})")
    task = json.loads(path.read_text())
    task["dir"] = str(path.parent)
    if task["relation"] not in ah.RELATIONS:
        raise HarnessError(f"{path}: unknown relation {task['relation']!r}")
    task["cost_order"] = check_cost_order(task.get("cost_order", DEFAULT_COST_ORDER), str(path))
    return task


def best_baseline(task: dict) -> str:
    """The cheapest known result of an external tool, for the task list."""
    rows = [(b["tCount"], tool) for tool, b in task.get("baselines", {}).items()
            if isinstance(b.get("tCount"), int)]
    return "{} ({})".format(*min(rows)) if rows else "-"


def cmd_tasks(_args) -> None:
    print(f"{'task':26} {'n':>3} {'gates':>6} {'T':>5} {'CX':>5} rel  {'order':18} "
          f"{'split':9} best known T-count")
    for d in task_dirs():
        t = load_task(d.name)
        c = t["original_cost"]
        print(f"{t['name']:26} {t['qubits']:>3} {c['gateCount']:>6} {c['tCount']:>5} "
              f"{c['cxCount']:>5} {ah.RELATIONS[t['relation']][1]:4} "
              f"{','.join(t['cost_order']):18} {t.get('split', '?'):9} {best_baseline(t)}")


def write_task(name: str, qubits: int, original: list[str], fields: dict,
               baselines: dict | None = None) -> Path:
    """Write `opt-tasks/<name>/`. What a person added by hand to an existing task survives a
    re-import: its cost order, baselines, redactions and known leaks."""
    for g in original:
        if not ah.GATE_RE.match(g):
            raise HarnessError(f"{name}: cannot read the gate `{g}`")
        if any(int(w) >= qubits for w in g.split()[1:]):
            raise HarnessError(f"{name}: `{g}` is off a register of {qubits}")
    names = [g.split()[0] for g in original]
    task = {
        "name": name, "kind": "optimize", "qubits": qubits, "relation": "u",
        "cost_order": list(DEFAULT_COST_ORDER), "original_cost": python_cost(original),
        "gates": {g: names.count(g) for g in sorted(set(names))},
        "split": "dev", "family": name, "rung": None, "source": {}, "baselines": {},
        "holdout": {"modules": [], "redact": [], "delete": []}, "known_leaks": [],
    }
    out = tasks_dir() / name
    prev = json.loads((out / "task.json").read_text()) if (out / "task.json").exists() else {}
    task.update({k: prev[k] for k in ("relation", "cost_order", "baselines") if k in prev})
    task.update({k: v for k, v in fields.items() if v is not None})
    task["cost_order"] = check_cost_order(task["cost_order"], name)
    task["known_leaks"] = prev.get("known_leaks") or task["known_leaks"]
    task["holdout"]["redact"] = prev.get("holdout", {}).get("redact") or task["holdout"]["redact"]
    for tool, entry in (baselines or {}).items():  # the numbers are recomputed, the notes kept
        kept = {k: v for k, v in task["baselines"].get(tool, {}).items()
                if k in ("certified", "note") and v}
        task["baselines"][tool] = {**entry, **kept}
    out.mkdir(parents=True, exist_ok=True)
    (out / "task.json").write_text(json.dumps(task, indent=2, ensure_ascii=False) + "\n")
    (out / "Task.lean").write_text(TASK_LEAN.replace("{n}", str(qubits))
                                   .replace("{original}", ah.fmt_lean_list(original)))
    c = task["original_cost"]
    print(f"wrote {out.relative_to(ah.repo_root())}/ ({qubits} qubits, "
          f"{cost_words(c, task['cost_order'])})")
    return out


def twin_baseline(gates: list[str], relation: str, certified, note: str) -> dict:
    """What the other circuit of an equivalent pair costs: a known result for the task."""
    return {**python_cost(gates), "relation": relation, "certified": certified, "note": note}


def tool_name(source: dict, fallback: str) -> str:
    return str(source.get("optimiser") or source.get("pipeline") or source.get("generator")
               or fallback)


def cmd_import_pair(args) -> None:
    """A task from the JSON pair files the equivalence harness reads: the `original` only.
    The twin of an equivalent pair is recorded as a baseline, never shown to the agent."""
    pair = json.loads(Path(args.file).read_text())
    source = pair.get("source", {})
    baselines = {}
    if pair.get("expected") == "equiv" and pair.get("optimized"):
        baselines[tool_name(source, "twin")] = twin_baseline(
            pair["optimized"], pair.get("relation", "u"), False,
            f"the twin in {Path(args.file).name}")
    write_task(args.name or pair["name"], pair["qubits"], pair["original"], {
        "relation": args.relation, "cost_order": args.cost_order,
        "split": pair.get("split", "held-out"), "family": pair.get("family", pair["name"]),
        "rung": pair.get("rung"), "source": {**source, "pair": pair["name"]},
        "holdout": {"modules": [], "redact": [], "delete": pair.get("holdout_delete", [])},
        "known_leaks": pair.get("known_leaks", []),
    }, baselines)


def cmd_import_benchmark(args) -> None:
    """A task from the `original` of a promoted benchmark. Its optimised twin and the proof
    are in the repository, so this is a development task: the module is held out, and the
    twin is a baseline that is already certified."""
    rel = f"CircuitEq/Benchmarks/{args.module}.lean"
    n, original, optimized = ah.read_benchmark_defs(ah.repo_root() / rel)
    baselines = {args.pipeline or "repository twin": twin_baseline(
        optimized, "u", rel, "the benchmark's `optimized`, proved equivalent in the repository")}
    write_task(args.name, n, original, {
        "relation": args.relation, "cost_order": args.cost_order, "split": "dev",
        "family": args.family or args.name, "rung": args.rung,
        "source": {"module": rel, "pipeline": args.pipeline or ""},
        "holdout": {"modules": [f"CircuitEq.Benchmarks.{m}"
                                for m in [args.module] + args.also_hold_out],
                    "redact": [], "delete": []},
        "known_leaks": [
            "the original is a promoted benchmark of this repository, whose optimised twin and "
            "its proof are in the repository and its history, so a model may have seen both; "
            "removed from the run copy: the module, README.md, benchmarks/, and the window "
            "table of scripts/certificate.py"],
    }, baselines)


def cmd_import_task(args) -> None:
    """A task from the `original` of a task of the equivalence harness, with its hold-out."""
    src = ah.load_task(args.task)
    n, original, optimized = ah.read_benchmark_defs(Path(src["dir"]) / "Task.lean")
    source = src.get("source", {})
    baselines = {}
    if src.get("expected") == "equiv":
        baselines[tool_name(source, "twin")] = twin_baseline(
            optimized, src["relation"], source.get("module", False),
            f"the twin of the equivalence task `{src['name']}`")
    holdout = src.get("holdout", {})
    write_task(args.name or src["name"], n, original, {
        "relation": args.relation, "cost_order": args.cost_order,
        "split": src.get("split", "dev"), "family": src.get("family"), "rung": src.get("rung"),
        "source": {**source, "equivalence_task": src["name"]},
        "holdout": {"modules": holdout.get("modules", []), "redact": holdout.get("redact", []),
                    "delete": holdout.get("delete", [])},
        "known_leaks": src.get("known_leaks", []),
    }, baselines)


def cmd_baseline(args) -> None:
    """Record what an external tool reaches on a task. Analysis only: no run reads it."""
    path = tasks_dir() / args.task / "task.json"
    load_task(args.task)
    task = json.loads(path.read_text())
    given = {"tCount": args.tcount, "cxCount": args.cx, "gateCount": args.gates,
             "relation": args.relation, "certified": args.certified, "note": args.note}
    old = task.setdefault("baselines", {}).get(args.tool, {})
    entry = {"relation": "u", "certified": False, **old,
             **{k: v for k, v in given.items() if v is not None}}
    if not isinstance(entry.get("tCount"), int):
        raise HarnessError("a new baseline needs --tcount")
    task["baselines"][args.tool] = entry
    path.write_text(json.dumps(task, indent=2, ensure_ascii=False) + "\n")
    print(f"{args.task}: {args.tool} -> {task['baselines'][args.tool]}")


# --------------------------------------------------------------------------
# setup: the shared workspace, with this harness's files
# --------------------------------------------------------------------------

def render_solution(task: dict) -> str:
    return (SOLUTION_LEAN.replace("{n}", str(task["qubits"]))
            .replace("{sym}", ah.RELATIONS[task["relation"]][1])
            .replace("{proof}", STUB_PROOFS[task["relation"]]))


def render_prompt(task: dict, budget_min: int, memory_gb: int, subagents: bool,
                  python_env: Path | None = None) -> str:
    return ah.render_prompt(task, budget_min, memory_gb, subagents, python_env, PROMPT_FILE, (
        ("{cost_clause}", cost_clause(task["cost_order"])),
        ("{original_cost}", cost_words(task["original_cost"], task["cost_order"]))))


def setup_run(args, task: dict) -> dict:
    """The equivalence harness's setup with this task's files in place of its own, then two
    things it does not need: the cost of `original` measured in Lean, so the numbers a run is
    compared against come from the same judge, and a pristine clone for the final judge."""

    def customise(ws: Path, run: dict) -> None:
        (ws / "Harness" / "Cost.lean").write_text(COST_LEAN)
        (ws / "Harness.lean").write_text("import Harness.Task\nimport Harness.Cost\n")
        (ws / "Solution.lean").write_text(render_solution(task))
        python_env = Path(run["python_env"]) if run["python_env"] else None
        (ws / "TASK.md").write_text(render_prompt(task, args.budget_min, args.memory_gb,
                                                  args.subagents, python_env))
        shutil.copyfile(SCRIPT, ws / ".harness" / "optimizer_harness.py")
        (ws / "submit").write_text(SUBMIT_SH)
        (ws / "submit").chmod(0o755)
        run.update(kind="optimize", harness_version=OPT_HARNESS_VERSION,
                   shared_harness_version=ah.HARNESS_VERSION,
                   instrument=ah.instrument_hash(getattr(args, "agent", "claude"), PROMPT_FILE),
                   cost_order=task["cost_order"], original_cost=task["original_cost"])
        in_run = json.loads((ws / ".harness" / "run.json").read_text())
        in_run.update(kind="optimize", cost_order=task["cost_order"],
                      original_cost=task["original_cost"])
        (ws / ".harness" / "run.json").write_text(json.dumps(in_run, indent=2))

    run = ah.setup_run(args, task, customise)
    root, ws, meta = Path(run["ws"]).parent, Path(run["ws"]), Path(run["meta"])
    print(f"[{run['run_id']}] measuring `original` with the judge's cost functions (seconds)")
    cost, reasons = measure_cost(ws, "original", meta / "setup.log", args.setup_timeout_min * 60,
                                 args.memory_gb * 1024, watch=True)
    (ws / JUDGE_FILE).unlink(missing_ok=True)
    if cost != task["original_cost"]:
        raise HarnessError(f"Lean measures `original` at {cost}, task.json says "
                           f"{task['original_cost']}. " + "; ".join(reasons))
    ah.clone_tree(ws, root / "pristine")
    return run


def cmd_setup(args) -> None:
    run = setup_run(args, load_task(args.task))
    print(f"workspace: {run['ws']}\nprompt:    {run['meta']}/prompt.md\n"
          f"The clock is not running. Judge it later with: judge {run['run_id']}")


# --------------------------------------------------------------------------
# judge
# --------------------------------------------------------------------------

def measure_cost(ws: Path, circuit: str, log: Path, timeout_s: float, limit_mb: int,
                 watch: bool) -> tuple[dict | None, list[str]]:
    """The cost of `Quantum.Circuit.Harness.<circuit>` by `Harness/Cost.lean`. `#eval` finds
    the numbers and the kernel confirms them; only the confirmation counts, so compiled code
    that disagrees with the definition (an `implemented_by`, say) gets a rejection, not a
    cheaper score."""
    imports = "import Harness.Cost\n" + ("import Solution" if circuit == "optimized"
                                         else "import Harness.Task")
    judge = ws / JUDGE_FILE
    if not (ws / ".lake" / "build" / "lib" / "lean" / "Harness" / "Cost.olean").exists():
        ah.run_guarded(["lake", "build", "Harness"], ws, log, timeout_s, limit_mb, watch)
    judge.write_text(MEASURE_LEAN.replace("{imports}", imports).replace("{circuit}", circuit))
    rc, out = ah.run_guarded(["lake", "env", "lean", JUDGE_FILE], ws, log, timeout_s, limit_mb,
                             watch)
    found = MEASURE_RE.search(out)
    if rc != 0 or found is None:
        return None, [f"the cost of `{circuit}` could not be evaluated (it must be a circuit "
                      "that `#eval` can compute):\n" + out[-1500:]]
    cost = dict(zip(COSTS, (int(v) for v in found.groups())))
    text = CONFIRM_LEAN.replace("{imports}", imports).replace("{circuit}", circuit)
    for key, value in cost.items():
        text = text.replace("{" + key + "}", str(value))
    judge.write_text(text)
    rc, out = ah.run_guarded(["lake", "env", "lean", JUDGE_FILE], ws, log, timeout_s, limit_mb,
                             watch)
    axioms = ah.parse_axioms(out, COST_THEOREM)
    if rc != 0 or axioms is None:
        return None, [f"the kernel did not confirm the measured cost of `{circuit}` "
                      f"({cost_words(cost, COSTS)}):\n" + out[-1500:]]
    extra = [a for a in axioms if a not in ah.ALLOWED_AXIOMS]
    if extra:
        return None, [f"the cost of `{circuit}` depends on {', '.join(extra)}"]
    return cost, []


def fingerprint(root: Path, rels: list[str]) -> dict[str, str]:
    return {rel: hashlib.sha256((root / rel).read_bytes()).hexdigest() for rel in rels}


def judge_solution(ws: Path, relation: str, manifest: dict[str, str], log: Path,
                   timeout_s: float, limit_mb: int, watch: bool) -> dict:
    """The optimisation judge: the rules and the proof of `equiv` exactly as the equivalence
    harness judges them (`ah.judge_workspace`: the files that changed, foreign imports, the
    scan of new Lean, then the restatement), then the cost of `optimized`. The report is that
    judge's, with `cost` added; `ACCEPT` means proved and measured."""
    report = ah.judge_workspace(ws, relation, ["equiv"], manifest, log, timeout_s, limit_mb, watch)
    report["cost"] = None
    if report["verdict"] == "ACCEPT":
        cost, reasons = measure_cost(ws, "optimized", log, timeout_s, limit_mb, watch)
        if cost is None:
            report.update(verdict="REJECT", reasons=reasons)
        report["cost"] = cost
    return report


# --------------------------------------------------------------------------
# submit: the judge inside a run, and the copies it keeps
# --------------------------------------------------------------------------

def read_snapshots(ws: Path, order) -> list[dict]:
    """The accepted submissions kept in a workspace, cheapest first, earliest among equals.
    The agent can write here, so an entry is a candidate for the final judge, not a result."""
    out = []
    root = ws / ACCEPTED
    for d in (sorted(root.iterdir()) if root.is_dir() else []):
        if not (d.name.isdigit() and (d / "cost.json").is_file() and (d / "files").is_dir()):
            continue
        try:
            info = json.loads((d / "cost.json").read_text())
            info.update(k=int(d.name), dir=str(d), score=score(info["cost"], order))
        except (ValueError, KeyError, TypeError):
            continue
        out.append(info)
    return sorted(out, key=lambda c: (c["score"], c["k"]))


def stage_snapshot(ws: Path) -> tuple[Path, dict[str, str]]:
    """Copy the submission aside before it is judged, so what is kept is what was judged."""
    stage = ws / ACCEPTED / f".pending-{uuid.uuid4().hex[:8]}"
    files = ah.solution_files(ws)
    for rel in files:
        (stage / "files" / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ws / rel, stage / "files" / rel)
    return stage, fingerprint(stage / "files", files)


def keep_snapshot(ws: Path, stage: Path, info: dict) -> int:
    """Give a judged copy its number, the next free one."""
    (stage / "cost.json").write_text(json.dumps(info, indent=2))
    for _ in range(100):
        k = 1 + max((int(d.name) for d in (ws / ACCEPTED).iterdir() if d.name.isdigit()), default=0)
        try:
            os.rename(stage, ws / ACCEPTED / str(k))
            return k
        except OSError:
            continue
    raise HarnessError("could not number the accepted submission")


def restore_snapshot(snapshot: Path, ws: Path) -> None:
    """Put a kept submission in place of whatever `Solution.lean` and `Solution/` hold.
    Nothing else of the copy is used, whatever it contains."""
    (ws / "Solution.lean").unlink(missing_ok=True)
    shutil.rmtree(ws / "Solution", ignore_errors=True)
    if (snapshot / "files" / "Solution.lean").is_file():
        shutil.copyfile(snapshot / "files" / "Solution.lean", ws / "Solution.lean")
    if (snapshot / "files" / "Solution").is_dir():
        shutil.copytree(snapshot / "files" / "Solution", ws / "Solution")


def cmd_submit(args) -> None:
    """What `./submit` runs inside a workspace. Advisory: the run is scored from outside,
    from the copies this keeps."""
    ws = Path(args.ws).resolve()
    run = json.loads((ws / ".harness" / "run.json").read_text())
    manifest = json.loads((ws / ".harness" / "manifest.json").read_text())
    order, original = run["cost_order"], run["original_cost"]
    kept = read_snapshots(ws, order)
    best = min([score(original, order)] + [c["score"] for c in kept])
    best_cost = next((c["cost"] for c in kept if c["score"] == best), original)

    stage, before = stage_snapshot(ws)
    try:
        report = judge_solution(ws, run["relation"], manifest, ws / ".harness" / "submit.log",
                                ah.JUDGE_TIMEOUT_S, run["memory_limit_mb"], watch=False)
    except BaseException:  # the harness refused, or the deadline came: leave no half copy
        shutil.rmtree(stage, ignore_errors=True)
        raise
    if report["verdict"] == "ACCEPT" and fingerprint(ws, ah.solution_files(ws)) != before:
        report.update(verdict="REJECT", reasons=[
            "`Solution.lean` or a file under `Solution/` changed while it was being judged, so "
            "nothing was kept; submit again and leave them alone until it returns"])
    elapsed = round(time.time() - run["started"]) if run.get("started") else None
    entry = {"time": ah.now(), "elapsed_s": elapsed, "verdict": report["verdict"],
             "cost": report["cost"], "improved": False, "snapshot": None,
             "reason": report["reasons"][0].splitlines()[0] if report["reasons"] else None}
    if report["verdict"] == "ACCEPT":
        entry["improved"] = score(report["cost"], order) < best
        entry["snapshot"] = keep_snapshot(ws, stage, {
            "cost": report["cost"], "time": entry["time"], "elapsed_s": elapsed,
            "axioms": report["axioms"], "files": before})
    else:
        shutil.rmtree(stage, ignore_errors=True)
    with (ws / ".harness" / "submissions.jsonl").open("a") as f:
        f.write(json.dumps(entry) + "\n")

    if report["verdict"] == "ACCEPT":
        print(f"ACCEPT: `equiv` is proved on the axioms {report['axioms']}, and `optimized` "
              f"costs {cost_words(report['cost'], order)}.")
        if entry["improved"]:
            print(f"This improves on the best so far ({cost_words(best_cost, order)}). It is kept "
                  f"as accepted submission {entry['snapshot']}; the cheapest accepted submission "
                  "is the score, so go on while time remains.")
        else:
            print(f"This does not improve on the best so far ({cost_words(best_cost, order)}), "
                  f"which still counts. Kept as accepted submission {entry['snapshot']}.")
    else:
        print("REJECT")
        for reason in report["reasons"]:
            print(" - " + reason)
        print(f"The best so far still counts: {cost_words(best_cost, order)}.")
    for w in report["warnings"]:
        print(f"note (a person will look at this): {w}")


# --------------------------------------------------------------------------
# The verdict of record
# --------------------------------------------------------------------------

def candidate_name(snapshot) -> str:
    """How a report names what was judged: a kept copy, or the working files."""
    if snapshot == "working files":
        return "the working files at the deadline"
    return f"accepted submission {snapshot}"


def resolve_run(ref: str) -> Path:
    root = ah.resolve_run(ref)
    run = json.loads((root / "meta" / "run.json").read_text())
    if run.get("kind") != "optimize":
        raise HarnessError(f"{root} is a run of the equivalence harness; use agent_harness.py")
    return root


def fresh_workspace(root: Path, dst: Path, manifest: dict[str, str]) -> None:
    """A clone of the workspace as it was before the agent started, checked against the
    manifest. The agent's own workspace is not reused: its build directory is not hashed."""
    if not (root / "pristine").is_dir():
        raise HarnessError(f"{root} has no pristine clone to judge in")
    dst.parent.mkdir(parents=True, exist_ok=True)
    ah.clone_tree(root / "pristine", dst)
    changed = [p for group in ah.changed_files(dst, manifest) for p in group]
    if changed:
        raise HarnessError("the pristine clone differs from the manifest: " + ", ".join(changed))


def final_judge(root: Path, max_candidates: int = 3, judge=judge_solution) -> dict:
    """Score a run from outside. The kept copies are candidates, cheapest first; each is put
    into a fresh clone and judged in full, and the first that passes is the result. What the
    copy claims to cost only orders the candidates: the score is what this judge measures."""
    meta, ws = root / "meta", root / "ws"
    run = json.loads((meta / "run.json").read_text())
    manifest = json.loads((meta / "manifest.json").read_text())
    order, original = run["cost_order"], run["original_cost"]
    snapshots = read_snapshots(ws, order)
    candidates = [c for c in snapshots if c["score"] <= score(original, order)]
    submissions = ah.read_submissions(ws)

    shutil.rmtree(root / "judge", ignore_errors=True)
    # The working files as the run left them are one more candidate, judged first because
    # their cost is unknown: an improvement the deadline cut off before `./submit` finished
    # still counts if it passes. Skipped when they are the untouched stub or a kept copy.
    working = None
    files = ah.solution_files(ws)
    now_fp = fingerprint(ws, files)
    kept_fps = [fingerprint(Path(c["dir"]) / "files", ah.solution_files(Path(c["dir"]) / "files"))
                for c in snapshots]
    stub_fp = fingerprint(meta / "snapshot", ah.solution_files(meta / "snapshot"))
    if files and now_fp != stub_fp and now_fp not in kept_fps:
        stage = root / "judge" / "working-files"
        for rel in files:
            (stage / "files" / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ws / rel, stage / "files" / rel)
        where = root / "judge" / "working"
        fresh_workspace(root, where, manifest)
        restore_snapshot(stage, where)
        report = judge(where, run["relation"], manifest, meta / "judge.log", ah.JUDGE_TIMEOUT_S,
                       run["memory_limit_mb"], True)
        working = {"snapshot": "working files", "claimed_cost": None, "elapsed_s": None,
                   "verdict": report["verdict"], "cost": report["cost"],
                   "reasons": report["reasons"], "report": report, "dir": where}

    attempts, won, won_dir = [], None, None
    for cand in candidates[:max_candidates]:
        if working and working["verdict"] == "ACCEPT" \
                and score(working["cost"], order) <= cand["score"]:
            break  # no kept copy claims to be cheaper than what the working files measure
        where = root / "judge" / str(cand["k"])
        fresh_workspace(root, where, manifest)
        restore_snapshot(Path(cand["dir"]), where)
        report = judge(where, run["relation"], manifest, meta / "judge.log", ah.JUDGE_TIMEOUT_S,
                       run["memory_limit_mb"], True)
        attempts.append({"snapshot": cand["k"], "claimed_cost": cand["cost"],
                         "elapsed_s": cand.get("elapsed_s"), "verdict": report["verdict"],
                         "cost": report["cost"], "reasons": report["reasons"]})
        if report["verdict"] == "ACCEPT":
            won, won_dir = report, where
            break
    tried = len(attempts)
    if working and working["verdict"] == "ACCEPT" and (
            won is None or score(working["cost"], order) < score(won["cost"], order)):
        won, won_dir = working["report"], working["dir"]
        attempts.append({k: working[k] for k in ("snapshot", "claimed_cost", "elapsed_s",
                                                 "verdict", "cost", "reasons")})
    elif working:
        attempts.insert(0, {k: working[k] for k in ("snapshot", "claimed_cost", "elapsed_s",
                                                    "verdict", "cost", "reasons")})
        if won is not None:  # keep the winner last: the fields below read `attempts[-1]`
            attempts.append(attempts.pop(next(i for i, a in enumerate(attempts)
                                              if a["verdict"] == "ACCEPT"
                                              and a["snapshot"] != "working files")))

    improved = won is not None and score(won["cost"], order) < score(original, order)
    modified, deleted, added = ah.changed_files(ws, manifest)
    seen = won or {"axioms": None, "warnings": [], "modified": modified, "deleted": deleted,
                   "added": added}
    final = {
        "verdict": "ACCEPT" if won else "NONE", "claim": "equiv" if won else None,
        "axioms": seen["axioms"], "replayed": bool(won),
        "cost_order": order, "original_cost": original,
        "best_cost": won["cost"] if improved else original, "improved": improved,
        "best_snapshot": attempts[-1]["snapshot"] if won else None,
        "best_accept_s": attempts[-1]["elapsed_s"] if won else None,
        "attempts": attempts, "kept": len(snapshots),
        "cut_off_by_limit": [] if won else [c["k"] for c in candidates[tried:]],
        "improvements": [{"elapsed_s": s.get("elapsed_s"), "cost": s.get("cost"),
                          "snapshot": s.get("snapshot")} for s in submissions
                         if s.get("verdict") == "ACCEPT" and s.get("improved")],
        "submissions": submissions,
        "added": seen["added"], "modified": seen["modified"], "deleted": seen["deleted"],
        "warnings": seen["warnings"],
        "reasons": [(f"accepted submission {a['snapshot']} failed from outside: "
                     if a["snapshot"] != "working files" else
                     "the working files at the deadline did not pass: ") + a["reasons"][0]
                    for a in attempts if a["verdict"] != "ACCEPT" and a["reasons"]],
        "workspace_protected_changes": sorted(p for p in modified + deleted
                                              if p not in ah.EDITABLE),
    }
    if won and attempts[-1]["claimed_cost"] is not None \
            and won["cost"] != attempts[-1]["claimed_cost"]:
        final["reasons"].append(f"accepted submission {final['best_snapshot']} claims "
                                f"{attempts[-1]['claimed_cost']}, the judge measures {won['cost']}")
    # The diff to read before trusting the row is the scored solution's; the other one is
    # everything the agent left behind.
    ah.write_changes_diff(meta / "snapshot", won_dir or ws, meta / "changes.diff")
    ah.write_changes_diff(meta / "snapshot", ws, meta / "workspace.diff")
    (meta / "judge.json").write_text(json.dumps(final, indent=2, ensure_ascii=False))
    return final


def after(elapsed_s: int | None) -> str:
    return f"after {elapsed_s} s" if elapsed_s is not None else "with no clock running"


def print_report(run: dict, report: dict, root: Path) -> None:
    order = report["cost_order"]
    print(f"\n[{run['run_id']}] {run['task']} / {run['config']}: "
          + ("improved" if report["improved"] else "no certified improvement"))
    print(f"  original: {cost_words(report['original_cost'], order)}")
    print(f"  best certified: {cost_words(report['best_cost'], order)}"
          + (f" ({candidate_name(report['best_snapshot'])}, {after(report['best_accept_s'])}, "
             f"axioms {report['axioms']})" if report["improved"] else ""))
    for a in report["attempts"]:
        print(f"  judged from outside: {candidate_name(a['snapshot'])}: {a['verdict']}"
              + (f", {cost_words(a['cost'], order)}" if a["cost"] else ""))
    if report["cut_off_by_limit"]:
        print("  not judged, --max-candidates reached: accepted submissions "
              f"{report['cut_off_by_limit']}")
    for reason in report["reasons"]:
        print("  - " + reason.splitlines()[0])
    accepted = sum(s.get("verdict") == "ACCEPT" for s in report["submissions"])
    print(f"  submissions: {len(report['submissions'])}, accepted {accepted}, improvements: "
          + (", ".join(f"{cost_words(i['cost'], order)} {after(i['elapsed_s'])}"
                       for i in report["improvements"]) or "none"))
    if report["workspace_protected_changes"]:
        print(f"  the workspace ended with protected files changed (not part of the score): "
              f"{report['workspace_protected_changes']}")
    for w in report["warnings"]:
        print(f"  look at: {w}")
    print(f"  read the diff before trusting the score: {root / 'meta' / 'changes.diff'}")


def cmd_judge(args) -> None:
    root = resolve_run(args.run)
    report = final_judge(root, args.max_candidates)
    print_report(json.loads((root / "meta" / "run.json").read_text()), report, root)


# --------------------------------------------------------------------------
# run: setup, agent, judge, record
# --------------------------------------------------------------------------

def cmd_run(args) -> None:
    task = load_task(args.task)
    config = ah.agent_config(args.agent)
    model = args.model or config.get("default_model", "")
    run = setup_run(args, task)
    root, ws, meta = Path(run["ws"]).parent, Path(run["ws"]), Path(run["meta"])
    run.update(agent=args.agent, model=model, run_index=args.run_index)

    timed_out, agent_wall, dog = False, 0.0, None
    if args.agent != "none":
        timed_out, agent_wall, dog = ah.run_agent(args, run, config, model)
    else:  # pipeline only: submit the untouched stub once, the way an agent would
        sys.stdout.flush()
        subprocess.run(["./submit"], cwd=ws, check=False)

    (meta / "run.json").write_text(json.dumps(run, indent=2))
    record_run(root, timed_out=timed_out, agent_wall=agent_wall, dog=dog, note=args.note,
               results=args.results, max_candidates=args.max_candidates)


def record_run(root: Path, timed_out: bool = False, agent_wall: float | None = None,
               dog: "ah.Watchdog | None" = None, note: str = "", results: str | None = None,
               max_candidates: int = 3) -> None:
    """Judge a run from outside, append its row to `opt-results.jsonl`, and keep the scored
    solution with the diff a person should read."""
    meta = root / "meta"
    run = json.loads((meta / "run.json").read_text())
    task = load_task(run["task"])
    report = final_judge(root, max_candidates)
    accepted = [s for s in report["submissions"] if s.get("verdict") == "ACCEPT"]
    row = ah.result_row(root, run, report, {
        "kind": "optimize", "shared_harness_version": run.get("shared_harness_version"),
        "relation": run["relation"], "cost_order": report["cost_order"],
        "original_cost": report["original_cost"], "best_cost": report["best_cost"],
        "improved": report["improved"], "best_snapshot": report["best_snapshot"],
        "best_accept_s": report["best_accept_s"], "improvements": report["improvements"],
        "accepted": len(accepted), "judged": [{k: a[k] for k in ("snapshot", "verdict", "cost")}
                                              for a in report["attempts"]],
        "axioms": report["axioms"], "baselines": task.get("baselines", {}),
        "workspace_protected_changes": report["workspace_protected_changes"],
    }, timed_out, agent_wall, dog, note)
    out = Path(results) if results else ah.harness_dir() / "results"
    out.mkdir(parents=True, exist_ok=True)
    with (out / RESULTS_FILE).open("a") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")
    keep = out / run["run_id"]
    keep.mkdir(exist_ok=True)
    if report["best_snapshot"] is not None:
        source = root / "judge" / str(report["best_snapshot"])
        for rel in ah.solution_files(source):
            (keep / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / rel, keep / rel)
    for name in ("changes.diff", "judge.json"):
        shutil.copyfile(meta / name, keep / name)
    print_report(run, report, root)
    print(f"  recorded in {out / RESULTS_FILE} (set \"reviewed\" once you have read the diff)")


def cmd_record(args) -> None:
    """For a run whose harness process died before judging: judge it and write its row."""
    record_run(resolve_run(args.run), note=args.note, results=args.results,
               max_candidates=args.max_candidates)


# --------------------------------------------------------------------------
# selftest: everything that needs neither lake nor an agent
# --------------------------------------------------------------------------

def cmd_selftest(_args) -> None:
    gates = ["H 0", "T 1", "Tdg 1", "CX 0 1", "S 0", "CX 1 0", "T 0"]
    assert python_cost(gates) == {"tCount": 3, "cxCount": 2, "gateCount": 7}
    assert list(COSTS) == ["tCount", "cxCount", "gateCount"], "the order `Cost.measure` lists"
    assert score({"tCount": 3, "cxCount": 2, "gateCount": 7}, ["tCount", "gateCount"]) == [3, 7]
    assert [2, 9] < [3, 0] and [3, 6] < [3, 7] and not [3, 7] < [3, 7], "lexicographic"
    for bad in ({"tCount": -1, "gateCount": 1}, {"tCount": "0", "gateCount": 1}, {"tCount": 1}):
        try:
            score(bad, ["tCount", "gateCount"])
            raise AssertionError(f"{bad} is not a cost")
        except (ValueError, KeyError):
            pass
    for order in (["tCount"], ["tCount", "gateCount"], ["tCount", "cxCount", "gateCount"]):
        clause = cost_clause(check_cost_order(order, "selftest"))
        assert all(COSTS[k][0] in clause and f"`{k}`" in clause for k in order), clause
    for bad_order in ([], ["tCount", "tCount"], ["depth"]):
        try:
            check_cost_order(bad_order, "selftest")
            raise AssertionError(f"{bad_order} is not a cost order")
        except HarnessError:
            pass
    assert cost_words({"tCount": 3, "cxCount": 2, "gateCount": 7}, ["tCount", "gateCount"]) \
        == "T-count 3, gate count 7 (CNOT count 2)"
    assert MEASURE_RE.search("warning: x\n[21, 18, 45]\n").groups() == ("21", "18", "45")
    assert MEASURE_RE.search("[21, 18]\n") is None
    lean = "import A.B\n  public import C\nimport all D.E\n-- x\ndef import_ := 1"
    assert ah.IMPORT_RE.findall(lean) == ["A.B", "C", "D.E"]
    for relation in ah.RELATIONS:
        text = render_solution({"qubits": 3, "relation": relation})
        assert "{" not in text and ah.RELATIONS[relation][1] in text, text
    confirm = CONFIRM_LEAN.replace("{circuit}", "optimized")
    assert confirm.count("Quantum.Circuit.Harness.optimized") == 3 and "decide +kernel" in confirm
    assert all(len(line) <= 100 for t in (COST_LEAN, CONFIRM_LEAN, MEASURE_LEAN, SOLUTION_LEAN)
               for line in t.splitlines())

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / "run"
        ws, meta, pristine = root / "ws", root / "meta", root / "pristine"
        for d in (pristine / "Harness", pristine / ".harness", meta):
            d.mkdir(parents=True)
        (pristine / "Harness" / "Task.lean").write_text("def original := 0\n")
        (pristine / "Harness" / "Cost.lean").write_text("def cost := 0\n")
        (pristine / "Solution.lean").write_text("cost 5 9\n")
        manifest = ah.build_manifest(pristine)
        (meta / "manifest.json").write_text(json.dumps(manifest))
        shutil.copytree(pristine, meta / "snapshot")
        shutil.copytree(pristine, ws)
        order, original = ["tCount", "gateCount"], {"tCount": 5, "cxCount": 0, "gateCount": 9}
        (meta / "run.json").write_text(json.dumps({
            "run_id": "selftest", "kind": "optimize", "task": "none", "config": "full",
            "relation": "u", "memory_limit_mb": 1, "cost_order": order, "original_cost": original}))

        # The files of a submission, the copy that is kept, and its restoration.
        (ws / "Solution").mkdir()
        (ws / "Solution" / "Lemmas.lean").write_text("import Harness.Task\nimport Solution.More\n")
        (ws / "Scratch.lean").write_text("-- not part of a submission\n")
        assert ah.solution_files(ws) == ["Solution.lean", "Solution/Lemmas.lean"]
        assert ah.foreign_imports(ws, manifest) == []
        (ws / "Solution.lean").write_text("import Scratch\n-- import Harness.Judge\ncost 4 9\n")
        foreign = ah.foreign_imports(ws, manifest)
        assert len(foreign) == 1 and "Scratch" in foreign[0], "the commented import does not count"
        (ws / "Harness" / "Judge.lean").write_text("theorem planted : False := sorry\n")
        (ws / "Solution.lean").write_text("import Harness.Judge\ncost 4 9\n")
        assert "Harness.Judge" in ah.foreign_imports(ws, manifest)[0], "the judge's own module"
        report = judge_solution(ws, "u", manifest, ws / "log", 1, 1, watch=False)
        assert report["verdict"] == "REJECT" and report["cost"] is None and report["broke_rules"]
        assert not (ws / "Harness" / "Judge.lean").exists(), "removed before any build"

        def keep(text: str, cost: dict, lemma: str | None = None) -> int:
            (ws / "Solution.lean").write_text(text)
            (ws / "Solution" / "Lemmas.lean").write_text(lemma or "-- lemmas\n")
            stage, files = stage_snapshot(ws)
            assert fingerprint(ws, ah.solution_files(ws)) == files
            return keep_snapshot(ws, stage, {"cost": cost,
                                             "elapsed_s": 60 * len(read_snapshots(ws, order))})

        assert keep("cost 5 9\n", {"tCount": 5, "cxCount": 0, "gateCount": 9}) == 1
        assert keep("cost 3 9\n", {"tCount": 3, "cxCount": 0, "gateCount": 9}) == 2
        assert keep("cost 2 8 broken\n", {"tCount": 2, "cxCount": 0, "gateCount": 8}) == 3
        assert keep("cost 3 7\n", {"tCount": 3, "cxCount": 0, "gateCount": 7}) == 4
        assert keep("cost 9 9\n", {"tCount": 9, "cxCount": 0, "gateCount": 9}) == 5
        (ws / ACCEPTED / "6" / "files").mkdir(parents=True)
        (ws / ACCEPTED / "6" / "cost.json").write_text('{"cost": {"tCount": "0"}}')
        (ws / ACCEPTED / ".pending-dead" / "files").mkdir(parents=True)
        assert [c["k"] for c in read_snapshots(ws, order)] == [3, 4, 2, 1, 5], "cheapest first"
        assert not any(p.startswith(".harness/accepted") for p in ah.build_manifest(ws))

        # The final judge with a stand-in for Lean: a copy passes unless it says `broken`, and
        # its cost is what its first line says. The working files are left broken.
        (ws / "Solution.lean").write_text("garbage\n")
        (ws / "Harness" / "Task.lean").write_text("def original := 1\n")
        seen = []

        def fake_judge(where, relation, manifest_, log, timeout_s, limit_mb, watch):
            modified, deleted, added = ah.changed_files(where, manifest_)
            assert modified == ["Solution.lean"] and not deleted
            words = (where / "Solution.lean").read_text().split()
            seen.append(words)
            ok = words[:1] == ["cost"] and "broken" not in words
            cost = ({"tCount": int(words[1]), "cxCount": 0, "gateCount": int(words[2])}
                    if ok else None)
            return {"verdict": "ACCEPT" if ok else "REJECT", "claim": "equiv" if ok else None,
                    "axioms": list(ah.ALLOWED_AXIOMS) if ok else None,
                    "reasons": [] if ok else ["`lake build Solution` failed"], "warnings": [],
                    "modified": modified, "deleted": deleted, "added": added, "broke_rules": False,
                    "cost": cost if ok else None}

        final = final_judge(root, 3, fake_judge)
        assert seen[0] == ["garbage"], "the working files at the deadline are judged first"
        assert [w[1:3] for w in seen[1:]] == [["2", "8"], ["3", "7"]], \
            "the next cheapest on failure"
        assert final["improved"] and final["best_snapshot"] == 4 and final["best_accept_s"] == 180
        assert final["best_cost"] == {"tCount": 3, "cxCount": 0, "gateCount": 7}
        assert final["cut_off_by_limit"] == [] and len(final["reasons"]) == 2, final
        assert final["reasons"][0].startswith("the working files at the deadline did not pass")
        assert final["workspace_protected_changes"] == ["Harness/Task.lean"]
        assert "cost 3 7" in (meta / "changes.diff").read_text()
        assert "garbage" in (meta / "workspace.diff").read_text()
        assert (root / "judge" / "4" / "Harness" / "Task.lean").read_text() == "def original := 0\n"

        # Working files that pass and are cheaper than every kept copy are the score; no kept
        # copy is judged, since none claims to be cheaper. Equal to a kept copy: not judged twice.
        (ws / "Solution.lean").write_text("cost 1 9\n")
        seen.clear()
        final = final_judge(root, 3, fake_judge)
        assert [w[1:3] for w in seen] == [["1", "9"]] and final["best_snapshot"] == "working files"
        assert final["best_cost"] == {"tCount": 1, "cxCount": 0, "gateCount": 9}
        assert final["improved"]
        shutil.copyfile(ws / ACCEPTED / "4" / "files" / "Solution.lean", ws / "Solution.lean")
        shutil.copytree(ws / ACCEPTED / "4" / "files" / "Solution", ws / "Solution",
                        dirs_exist_ok=True)
        seen.clear()
        final = final_judge(root, 3, fake_judge)
        assert final["best_snapshot"] == 4 and all(w != ["garbage"] for w in seen)
        assert sum(w[1:3] == ["3", "7"] for w in seen) == 1, "a kept copy is not judged twice"
        (ws / "Solution.lean").write_text("garbage\n")

        final = final_judge(root, 1, fake_judge)
        assert not final["improved"] and final["best_cost"] == original
        assert final["verdict"] == "NONE"
        assert final["cut_off_by_limit"] == [4, 2, 1]
        shutil.rmtree(ws / ACCEPTED)
        final = final_judge(root, 3, fake_judge)
        assert not final["improved"] and final["best_cost"] == original
        assert [a["snapshot"] for a in final["attempts"]] == ["working files"]
        (pristine / "Harness" / "Task.lean").write_text("def original := 1\n")
        keep("cost 1 1\n", {"tCount": 1, "cxCount": 0, "gateCount": 1})
        try:
            final_judge(root, 3, fake_judge)
            raise AssertionError("a pristine clone that differs from the manifest must be refused")
        except HarnessError:
            pass

    for d in task_dirs():
        task = load_task(d.name)
        n, original = ah.read_circuit_def(d / "Task.lean", "original")
        assert n == task["qubits"] and task.get("kind") == "optimize", d.name
        assert python_cost(original) == task["original_cost"], f"{d.name}: original_cost"
        assert sum(task["gates"].values()) == len(original), f"{d.name}: gates"
        assert "def optimized" not in (d / "Task.lean").read_text(), f"{d.name}: the twin leaks"
        prompt = render_prompt(task, 30, 6, False, Path("/nonexistent"))
        assert "{" not in prompt and cost_words(task["original_cost"], task["cost_order"]) in prompt
        for tool, b in task.get("baselines", {}).items():
            assert isinstance(b.get("tCount"), int), (d.name, tool)
            assert b.get("relation") in ah.RELATIONS, (d.name, tool)
    print("selftest passed")


# --------------------------------------------------------------------------

def add_import_options(p: argparse.ArgumentParser) -> None:
    p.add_argument("--relation", choices=tuple(ah.RELATIONS),
                   help="what `equiv` must state (default `u`); `p` needs a library that "
                        "composes `≡ₚ`")
    p.add_argument("--cost-order", nargs="+", choices=tuple(COSTS), metavar="COST",
                   help=f"lexicographic, from {', '.join(COSTS)} "
                        f"(default: {' '.join(DEFAULT_COST_ORDER)})")


def add_judge_options(p: argparse.ArgumentParser) -> None:
    p.add_argument("--max-candidates", type=int, default=3,
                   help="how many accepted submissions the final judge tries, cheapest first")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("tasks").set_defaults(fn=cmd_tasks)
    sub.add_parser("selftest").set_defaults(fn=cmd_selftest)

    p = sub.add_parser("import-pair")
    p.add_argument("file",
                   help="JSON: name, qubits, original (gate strings); `optimized` is a baseline")
    p.add_argument("--name", help="task name (default: the pair's)")
    add_import_options(p)
    p.set_defaults(fn=cmd_import_pair)

    p = sub.add_parser("import-benchmark")
    p.add_argument("module", help="module name under CircuitEq/Benchmarks, e.g. Tof3")
    p.add_argument("--name", required=True)
    p.add_argument("--family")
    p.add_argument("--rung", type=int)
    p.add_argument("--pipeline", help="what made the module's `optimized`, e.g. `pyzx teleport`")
    p.add_argument("--also-hold-out", nargs="+", default=[], metavar="MODULE",
                   help="other benchmark modules that give this one's answer away")
    add_import_options(p)
    p.set_defaults(fn=cmd_import_benchmark)

    p = sub.add_parser("import-task")
    p.add_argument("task", help="a task under benchmarks/harness/tasks")
    p.add_argument("--name", help="task name (default: the same)")
    add_import_options(p)
    p.set_defaults(fn=cmd_import_task)

    p = sub.add_parser("baseline")
    p.add_argument("task")
    p.add_argument("tool", help="what produced the circuit, e.g. `pyzx full_reduce`")
    p.add_argument("--tcount", type=int, help="needed for a new entry; an old one is updated")
    p.add_argument("--gates", type=int)
    p.add_argument("--cx", type=int)
    p.add_argument("--relation", choices=tuple(ah.RELATIONS),
                   help="how the tool's output relates to the original (default `u`)")
    p.add_argument("--certified", help="where a Lean proof of that lives, if anywhere")
    p.add_argument("--note")
    p.set_defaults(fn=cmd_baseline)

    p = sub.add_parser("setup")
    ah.add_run_options(p)
    p.set_defaults(fn=cmd_setup)

    p = sub.add_parser("run")
    ah.add_run_options(p)
    ah.add_agent_options(p)
    add_judge_options(p)
    p.add_argument("--results", help="directory for the row and the kept solution "
                                     "(default: benchmarks/harness/results)")
    p.set_defaults(fn=cmd_run)

    p = sub.add_parser("judge")
    p.add_argument("run", help="a run id, or the path of a run directory")
    add_judge_options(p)
    p.set_defaults(fn=cmd_judge)

    p = sub.add_parser("record")
    p.add_argument("run", help="a run id, or the path of a run directory")
    p.add_argument("--note", default="")
    p.add_argument("--results")
    add_judge_options(p)
    p.set_defaults(fn=cmd_record)

    p = sub.add_parser("submit")
    p.add_argument("--ws", required=True)
    p.set_defaults(fn=cmd_submit)

    args = parser.parse_args()
    try:
        args.fn(args)
    except HarnessError as e:
        sys.exit(f"harness: {e}")


if __name__ == "__main__":
    main()
