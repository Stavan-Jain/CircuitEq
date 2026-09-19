# Agent harness: the equivalence-checking task (draft)

Measures how far an AI agent gets, with this library, at deciding whether two
Clifford+T circuits are equivalent. A task is a pair of circuits; the answer
is a Lean proof of the claim or of its negation; the Lean kernel is the
judge, so a task needs no ground truth. `QUEUE.md` item 1 is the work item,
`ROADMAP.md` ("What is strictly needed, and what the library adds") is the
reason it exists.

**Status.** A draft that has run end to end three times (19 September 2026)
on `peephole_8q_1000g_s1`, 1000 gates against 752 on eight qubits, with
`claude-fable-5-1`. The first two runs (20 minutes) ended without a
certificate and exposed the faults listed under "What the first runs
taught". The third (45 minutes, harness 0.4, library `a9a80ed`) was
**proved**: `./submit equiv` accepted after 16.9 minutes, the agent stopped
at 17.5, the judge from outside agreed, kernel replay included; $3.33, peak
Lean memory 1.8 GB, nothing killed (`results/results.jsonl`, the solution
under `results/20260919-171348-e58dbd/`). One run per configuration says
little: the budget, the playbook's advice and the prompt all changed between
the second run and the third. Not exercised yet: the `core` configuration,
the memory watchdog firing, the deadline kill, a refutation.

## What is fixed and what varies

Three things can change between two runs, and every result row records all
three, so that a difference can be attributed.

- **The harness** (`HARNESS_VERSION`): `scripts/agent_harness.py`, the one
  prompt in `PROMPT.md`, the agent configuration in `agents/`. The prompt
  says what the goal is, what counts, the rules and the budget. It never
  names a tool or a proof technique, because those change with the library.
- **The library** (a commit): built once by `prepare`, cloned for every run,
  together with `PLAYBOOK.md` at the repository root. The playbook is the
  prover's guide: what exists, what it costs, in which order to try it. It
  is installed as the run's `CLAUDE.md` (the repository's own `CLAUDE.md`
  tells its reader to work on `QUEUE.md`, which is wrong here) and it is
  versioned with the library: a tool the playbook does not mention does not
  exist for the agent, so update it in the commit that adds the tool.
- **The model** (a pinned id, `claude-fable-5-1` by default, not an alias).

Two configurations of the library: `full`, and `core`, which strips the run
copy down to the modules up to `Semantics.lean` and uses
`PLAYBOOK.core.md`. Their difference is the project's hypothesis.

## Running it

```bash
python3 scripts/agent_harness.py selftest
python3 scripts/agent_harness.py tasks
python3 scripts/agent_harness.py prepare            # once per library commit; minutes
python3 scripts/agent_harness.py run rep3_phaseflip --agent none   # pipeline only
python3 scripts/agent_harness.py run tof_3 --budget-min 30 --max-usd 20
python3 scripts/agent_harness.py run tof_3 --config core
python3 scripts/agent_harness.py setup tof_3        # a workspace to inspect or drive by hand
python3 scripts/agent_harness.py judge <run-id>
python3 scripts/agent_harness.py digest <run-id>    # what the agent said and did
python3 scripts/agent_harness.py record <run-id>    # judge and record a run whose harness died
```

Start `run` from a plain terminal, or detached (`nohup … &`): a run started
as a background job of a Claude Code session dies when that session ends.

`prepare` exports the commit with `git archive` (so no `.git` reaches a run),
links `.lake/packages` to a directory that already holds a compiled mathlib,
and runs `lake build` once. It works from committed state: commit before you
prepare. Bases and runs live under `~/.circuiteq-harness`
(`CIRCUITEQ_HARNESS_HOME`); on APFS a run is a copy-on-write clone of its
base. Run one at a time and not beside other Lean builds: memory is the
limit on this machine, and a swapping machine ruins the timing.

**Lake is never allowed to fetch.** Before every lake call the harness checks
that the workspace's `.lake/packages` resolves to a compiled mathlib, and
`prepare` checks that every revision pinned by `lake-manifest.json` is the
one checked out there. If not, it refuses; it does not let lake clone or
build mathlib.

## One run, step by step

1. Clone the base. Delete what gives answers away: `README.md`,
   `ROADMAP.md`, `QUEUE.md`, `benchmarks/`, the task's own module under
   `CircuitEq/Benchmarks/` with its import and its build products, the window
   table in `scripts/certificate.py`, and the task's own redactions.
2. Write the harness's files: `Harness/Task.lean` (the two circuits),
   `Solution.lean` (the claim as `equiv`, its negation as `not_equiv`, both
   `sorry`), `TASK.md` (the prompt), `CLAUDE.md` (the playbook), `./submit`,
   `./time-left`, and two `lean_lib`s appended to `lakefile.toml`. Nothing
   the agent can read says which task this is, or whether it is a mutant.
3. Build the workspace, outside the clock, and hash every file.
4. Start the clock and the agent. A watchdog kills any `lean` process under
   the agent that passes the memory limit (6 GB by default) and the run is
   stopped at the budget plus a short grace.
5. Judge from outside the workspace, write `changes.diff`, append a row to
   `results/results.jsonl`, and keep the solution under `results/<run-id>/`.

## The judge, and what is left to you

`./submit` inside the run and the final judge run the same check:

- no file that existed at the start changed, except `Solution.lean`;
- the solution's modules import only what existed at the start or lives
  under `Solution/`, and an agent-written `Harness/Judge.lean` is deleted
  before the build. The kernel replay below covers the `Solution` modules
  only, and without this rule a false claim was accepted: its lemma sat in
  a new module outside `Solution/`, behind `debug.skipKernelTC` (found by
  the agent that built the optimisation harness, reproduced and fixed on
  19 September 2026; the same cheat under `Solution/` is rejected by the
  replay, which names the module);
- the agent's Lean sources do not contain `native_decide`, a `debug.*`
  option, a compiler-trust primitive, an `axiom`, `implemented_by` or
  `extern` (comments are stripped first);
- `lake build Solution` succeeds;
- the harness writes `Harness/Judge.lean`, which restates the claim against
  its own circuits with fully qualified names and no notation and gives the
  agent's theorem as the proof. It typechecks only if the agent proved
  exactly that statement about exactly those circuits;
- `#print axioms` of that restatement lists nothing beyond `propext`,
  `Classical.choice`, `Quot.sound`;
- `LEAN_NUM_THREADS=1 lake env leanchecker -v Solution` replays the agent's
  modules through the kernel, in a process where none of their options or
  meta code runs. This is what catches a declaration that skipped the
  kernel: tested with a false claim behind `debug.skipKernelTC`, which
  builds clean and reports the three standard axioms, and which the replay
  rejects with a kernel error naming the declaration.

The outcome is `proved`, `refuted`, `no_certificate`, or `invalid` (a rule
was broken). `first_accept_s` is when `./submit` first said ACCEPT.

The text scan is an early warning, not a defence (an option can be set from
meta code); the replay is the defence. One gap remains in this harness: it
judges in the agent's own workspace, so it trusts the build products under
`.lake/` there. The optimisation harness judges in a fresh clone of the
workspace as it was before the agent started; this one should too. What the replay does not do: it
trusts the library and mathlib as built, and it is the same kernel again,
not an independent checker (SafeVerify, `leanprover/comparator`: `QUEUE.md`,
"Later"). So still read `changes.diff` before you believe a row, then set its
`"reviewed"` field. The final report lists what to look at: any `set_option`
outside a short harmless list, `unsafe`, `#eval`, `run_cmd`, `initialize`,
file or process access from Lean, and new notation.

## What the agent can touch

`agents/claude.json` starts Claude Code headless with
`--permission-mode acceptEdits` and an allow list that includes `Bash`.
Nobody is there to answer a permission prompt, so this is what lets the
agent run `lake` and `./submit` at all, and it is also a shell on this
machine that only the prompt confines to the run directory. The deny list
removes the web tools, `git`, `curl`, `wget`, `lake update`,
`lake exe cache`, the language server's network search tools and its
`lean_build` (which can fetch a cache). Tighten the allow list to command
patterns, or run inside a container or a separate user account, if that is
not the posture you want. Subagent tools are denied unless the run passes
`--subagents`; subagents would share one lake workspace, which the library's
one-lake-at-a-time rule does not survive, so give them their own workspaces
before relying on that switch.

## What the first runs taught

- **The agent killed its own harness.** Looking for a stuck job of its own,
  it listed the machine's processes, killed the harness by pid, and later
  ran `pkill -x lean; pkill -x lake`, which would have taken down any other
  session's Lean build. From then on nothing enforced the deadline or the
  memory limit. Now `kill`, `pkill` and `killall` are denied, the prompt
  says whose processes share the machine, and the harness ignores `SIGTERM`
  while an agent runs. None of that is isolation: an agent with a shell
  under your account can still reach everything you can. A separate user
  account or a container is the real fix.
- **The environment is part of the instrument.** The machine's `python3` has
  no `numpy` or `pyzx`, which the library's alignment script imports, and
  the first run spent eight of its thirteen minutes working around that.
  The harness now offers `./python` from a virtualenv that has both
  (`--python-env`, `CIRCUITEQ_HARNESS_PYENV`, default
  `/tmp/circuiteq-pyzx-venv`) and records which one on the row. It also
  offers `./qasm` (`tools/qasm.py`, an exact converter between the Lean
  lists and OpenQASM 2, standard library only) and, when TZAP is installed
  (`CIRCUITEQ_HARNESS_TZAP`, default `~/.circuiteq-harness/envs/tzap`, see
  `notes/README.md`), `./tzap` as an untrusted oracle; the prompt names all
  three as facts about the machine, and the row records the TZAP version.
- **Judging the final state wastes budget.** The second run stopped its
  proof build and gave up with seven minutes left, to restore a stub that
  builds before the deadline. Not fixed yet: keep a copy of each accepted
  submission and judge the best one, so the working file may be in any
  state.
- **The Lean language server was offered and never used** (0 of 37 tool
  calls over both runs): at this size the work is search outside Lean.
  Tool calls are recorded per run, so this can be measured.
- What stopped the proof itself belongs to the library, not the harness:
  the alignment search does not finish on a 1000-gate pair, and a
  55-segment proof in one file ran past 4 GB.

## Tasks

`tasks/<name>/task.json` and `tasks/<name>/Task.lean`. Eight came first:
the five promoted pairs and a gate-deleted mutant of three of them (deleting
one gate of an equivalent pair always breaks it, under all three relations,
since no gate of the alphabet is a scalar). `expected` is for analysis only;
the judge never reads it.

```bash
python3 scripts/agent_harness.py import-benchmark Tof3 --name tof_3 --family tof --rung 3
python3 scripts/agent_harness.py import-benchmark Tof3 --name tof_3 --mutant 1
```

A first held-out pair, of the size the promoted benchmarks do not reach:

```bash
python3 scripts/peephole_pairs.py --qubits 8 --gates 1000 --seed 1 --out pair.json
python3 scripts/agent_harness.py import-pair pair.json
```

`scripts/peephole_pairs.py` draws a seeded random circuit over the whole
alphabet and makes its twin by a peephole pass that uses exactly the
library's commutation and cancellation rules plus one-wire phase fusions, so
the pair is equal by construction and keeps its skeleton, like phase-folding
output. `peephole_8q_1000g_s1` is 1000 gates against 752 on eight qubits, out
of reach of a brute-force basis decide. The generator is held out of the run.

The other eight are **development tasks**: their proofs are in this repository and
its history, and each `task.json` lists the leaks the hold-out cannot remove
(`known_leaks`). They are for debugging the harness and the playbook. The
measurement needs a held-out ladder of pairs that appear nowhere in the
repository, drawn from parametrised families (`tof_k`, `cuccaro_k`,
`barenco_tof_k`, seeded random circuits, TZAP on the Feynman suite) with
the largest rung solved as the metric, because a fixed set saturates. The
QASM-to-Lean translation for that is `lean_instructions` in
`scripts/check_pyzx_benchmarks.py`; an importer from QASM is the next piece.

## Not built yet

- Isolation of the agent (a separate account or a container), and judging
  the best accepted submission instead of the final state (above).
- The held-out ladder and the QASM importer (above).
- The baselines: the alignment script alone, one-line checker calls, QCEC
  and Feynman on the same pairs.
- Repeated runs and a summary table over `results.jsonl` (three runs per
  cell at least; one run says little).
- Which library declarations an accepted proof uses (the roadmap's flywheel
  record).
- Subagents with their own workspaces; the optimiser task, which needs
  `tCount` in Lean first (`QUEUE.md` item 2). (Drafted since, below, with
  cost functions the harness owns until the library has its own.)

# The optimisation harness (draft)

The second product of the roadmap ("Two products, one architecture"), as a
task for an agent. A task is one circuit, `original`, and a cost function.
The agent must produce a cheaper circuit `optimized` and a Lean proof of
`original ≡ᵤ optimized`. The kernel guarantees the equivalence, so only the
quality of the result depends on the agent, and no task needs a reference
answer. External optimisers (PyZX through `./python`, TZAP where it is
installed) are untrusted oracles: the agent may call them, and only what it
proves is scored.

`scripts/optimizer_harness.py` is the script, `PROMPT.optimize.md` the one
prompt, `opt-tasks/` the tasks, `results/opt-results.jsonl` the record.

**Status.** Built and tested by hand on 19 September 2026 against library
`a9a80ed`, with no agent: see "What was tested" below. No agent run yet.

## What is shared with the equivalence harness

`optimizer_harness.py` imports `agent_harness.py` and adds only what differs.
Shared, as the same code: the warm bases and `prepare`; the rule that lake
never fetches (`assert_lake_safe`, `run_guarded`, the dependency tripwire);
the memory watchdog; `setup_run` (the clone, the hold-out, `./python`,
`./time-left`, the playbook as `CLAUDE.md`, the build outside the clock, the
manifest and the snapshot), through one hook for the files that differ; the
protected-files check and the forbidden-text scan; the judge of `equiv`
(`judge_workspace`: build, restatement with fully qualified names, axioms,
kernel replay on one thread); the agent launch from `agents/*.json`, the
deadline, the `SIGTERM` handling (`run_agent`); `digest`; the attribution
fields of a result row (`result_row`); `changes.diff`. A copy of both scripts
runs inside every optimisation workspace. `HARNESS_VERSION` still names the
shared code and `OPT_HARNESS_VERSION` this harness (its prompt, its judge,
its agent configuration); a row records both, and its `instrument` hashes
`PROMPT.optimize.md` with the agent configuration.

What is fixed and what varies is the same three things, plus one that is
fixed per task: the cost order.

## Running it

```bash
python3 scripts/optimizer_harness.py selftest
python3 scripts/optimizer_harness.py tasks
python3 scripts/agent_harness.py prepare            # the bases are shared
python3 scripts/optimizer_harness.py run tiny_3q --agent none   # pipeline only
python3 scripts/optimizer_harness.py run tof_3 --budget-min 30 --max-usd 20
python3 scripts/optimizer_harness.py setup tof_3    # a workspace to drive by hand
python3 scripts/optimizer_harness.py judge <run-id>
python3 scripts/optimizer_harness.py record <run-id>  # a run whose harness died
python3 scripts/agent_harness.py digest <run-id>    # runs live side by side
```

`run … --agent none` sets up a workspace, submits the untouched stub once the
way an agent would, judges from outside and records: half a minute on any of
the tasks, the 1000-gate one included. `--results DIR` sends the row and the
kept solution somewhere else than `results/`, for tests.

## The workspace, the cost and the judge

The agent gets what the equivalence harness gives, with these differences.
`Harness/Task.lean` defines `original` only. `Harness/Cost.lean`, also owned
by the harness, defines the cost functions on `Circuit n`: `tCount` (gates
`T` and `Tdg`), `cxCount`, `gateCount`. They are the harness's definitions,
not the library's, which has none yet (`QUEUE.md` item 2). `Solution.lean`
starts as `def optimized : Circuit n := original` with
`theorem equiv : original ≡ᵤ optimized := Equivalent.refl _`, so a run
starts from a valid submission whose cost is the original's.

The cost of a task is lexicographic, `cost_order` in its `task.json`
(default `tCount`, then `cxCount`, then `gateCount`: T gates dominate a
fault-tolerant cost, two-qubit gates come next, and the total keeps an
optimiser from ignoring size), and the prompt states it exactly. The
agent never reports a cost. `./submit` and the final judge run the same
check:

- the equivalence harness's judge on the claim `equiv`, unchanged: nothing
  that existed at the start changed except `Solution.lean`, the text scan,
  `lake build Solution`, the restatement
  `Quantum.Circuit.Equivalent Quantum.Circuit.Harness.original
  Quantum.Circuit.Harness.optimized` proved by the agent's theorem, the three
  axioms, and `LEAN_NUM_THREADS=1 lake env leanchecker -v Solution`, which
  replays `Solution` and every module under `Solution/`;
- before that, two things this task needs: the judge's scratch module
  `Harness/Judge.lean` is deleted before the build, and a solution module that
  imports Lean code of the workspace that is neither a file that existed at
  the start nor under `Solution/` is rejected. Such a module would not be in
  the kept copy, is not replayed through the kernel, and may be the judge's
  own scratch module, which the manifest does not hash;
- then the cost. The judge evaluates `Cost.measure` on the agent's constant
  `Quantum.Circuit.Harness.optimized` with `#eval`, and states the numbers
  it read as a theorem with fully qualified names, proved by
  `decide +kernel`. The evaluation only finds the numbers; the kernel's
  confirmation is what counts, so compiled code that disagrees with the
  definition earns a rejection and not a cheaper score. The constant
  measured is the constant `equiv` is about, so the proof covers the cost.
  A circuit of 1000 gates is measured and confirmed in about four seconds.

`./submit` prints `ACCEPT` with the measured cost and whether it improves on
the best so far, or `REJECT` with the reason. It judges the working files in
place, and it is advisory.

**Anytime and monotone.** Before judging, `./submit` copies `Solution.lean`
and `Solution/` aside; if the verdict is `ACCEPT` and the working files still
hash the same, the copy becomes `.harness/accepted/<k>/` with its cost. The
score of a run is the cheapest accepted submission, so the working files may
be in any state at the deadline, which fixes what the second equivalence run
lost seven minutes to. The working files as the run left them are judged
once more as a last candidate, first because their cost is unknown, unless
they are the untouched stub or one of the kept copies: an improvement whose
`./submit` the deadline cut off still counts if it passes (tested with Lean:
an improvement never submitted was scored). The final judge trusts none of
this: the kept copies are candidates. It takes them cheapest first (the claimed cost only orders
them; copies that cost more than the original are skipped), puts each into a
fresh clone of `pristine/`, the workspace as it was before the agent started,
checked against the manifest, and judges it in full there. Nothing the agent
left in its build directory or outside `Solution.lean` and `Solution/` can
reach that clone; the price is that the solution is built again from source.
The first candidate that passes is the result; after
`--max-candidates` failures (default 3) it stops. A run never fails: with no
certified improvement its score is the cost of `original`, which the harness
measured in Lean during setup and compared with `task.json`.

A row of `results/opt-results.jsonl` has the attribution fields of the
equivalence harness (both versions, library commit, model, instrument,
budget, python environment, tool calls, agent cost) and: `cost_order`,
`original_cost`, `best_cost` (certified), `improved`, `best_snapshot`,
`best_accept_s`, `improvements` (time and cost of each accepted submission
that beat the best so far), `submissions`, `accepted`, `judged` (what the
final judge tried), the task's `baselines`, and
`workspace_protected_changes` (protected files the agent left changed, which
cannot affect the score and should still be looked at). The scored solution's
Lean files, `changes.diff` (the scored solution against the start; read it
before believing the row) and `judge.json` are kept under
`results/<run-id>/`; `workspace.diff`, everything the agent left behind,
stays in the run's `meta/`. The times and the submission log come from files
the agent can write; the score does not.

## Global phase

Optimisers preserve a circuit only up to a global phase: every output of
PyZX and TZAP on the 1000-gate circuit is phase-only (`notes/README.md`). The
relation is a field of the task, as in the equivalence harness:
`"relation": "p"` changes the stub, the prompt and the restatement to `≡ₚ`.
The three real starter tasks (`tof_3`, `barenco_tof_3`,
`peephole_8q_1000g_s1`) ask for `≡ₚ` (decided 19 September 2026); an exact
proof still counts, by `Equivalent.toUpToPhase`. What an agent can prove
depends on the library commit: at `a9a80ed` `≡ₚ` has no composition lemmas,
so a phase-only result is provable only by a whole-register decide on a few
qubits; with the branch `claude/phase-composition` (`≡ₚ[k]`, windows and
certificates up to phase, the Clifford phase gadget) it is provable piece by
piece. `tiny_3q` stays on `≡ᵤ` and `tiny_2q_phase` tests `"p"`.

## Tasks

`opt-tasks/<name>/task.json` and `Task.lean`. The JSON has the qubits, the
gate counts by kind, `original_cost`, `cost_order`, `relation`, the family
and rung, the provenance, the hold-out, `known_leaks`, and `baselines`: what
external tools reach on the same circuit, mostly uncertified, for comparison
only. No run reads them and no workspace contains them.

```bash
python3 scripts/optimizer_harness.py import-pair pair.json        # `original` only
python3 scripts/optimizer_harness.py import-benchmark Tof3 --name tof_3 \
    --family tof --rung 3 --pipeline "pyzx teleport" --also-hold-out BarencoTof3
python3 scripts/optimizer_harness.py import-task peephole_8q_1000g_s1
python3 scripts/optimizer_harness.py baseline tof_3 "pyzx full_reduce" \
    --tcount 15 --gates 51 --note "…"
```

`import-pair` reads the pair files of the equivalence harness and
`import-task` one of its tasks; the twin of an equivalent pair becomes a
baseline. A re-import keeps what a person wrote into the task (cost order,
baselines, redactions, known leaks).

| Task | Qubits | Gates | T-count | Known results (T-count) |
|---|---:|---:|---:|---|
| `tiny_3q` | 3 | 8 | 3 | by hand: 1, with 5 gates (the harness's test) |
| `tiny_2q_phase` | 2 | 5 | 2 | by hand: 0 up to a phase (the test of `"p"`) |
| `tof_3` | 5 | 45 | 21 | PyZX teleport 19, proved in the repository; PyZX `full_reduce` 15; TZAP 15 |
| `barenco_tof_3` | 5 | 60 | 28 | PyZX teleport 24, proved in the repository; PyZX `full_reduce` 16; TZAP 16 |
| `peephole_8q_1000g_s1` | 8 | 1000 | 257 | our peephole pass 127, proved by an agent in equivalence run `20260919-171348-e58dbd`; PyZX teleport 109 and `full_reduce` 101, both only up to a global phase |

Hold-out works as in the equivalence harness. For a task made from a
promoted benchmark, the optimised twin is in the repository: its module goes
with its build products, and `benchmarks/`, the README and the window table
of `scripts/certificate.py` go for every run. Checked on a `tof_3` workspace
by searching for pieces of the twin: two more leaks were found and closed.
`CircuitEq/Benchmarks/BarencoTof3.lean` is the same Toffoli decomposition
through the same PyZX pipeline, twin and proof included, so each of the two
Toffoli tasks holds out both modules; and the self-test of
`scripts/tcount_survey.py` carries the four windows of the `tof_3` proof,
which a task-level redaction removes. What stays is in `known_leaks`: three
test theorems in `CircuitEq/PhasePoly.lean` that state the `T 0, T 0 = S 0`
merge (redacting them would rebuild the largest module on every run), and
the fact that a model may have seen these pairs. They are development
tasks. `peephole_8q_1000g_s1` is held out: its twin and the proof an agent
found for it are under `benchmarks/`, which no run sees.

## What was tested

By hand, in workspaces the harness made from the warm base of `a9a80ed`,
with no agent:

- the untouched stub is accepted at the original's cost, on every task;
- on `tiny_3q`, `T 1, T 1` replaced by `S 1` and proved by
  `circuit_windows` is accepted at T-count 1 with 7 gates, and with the
  `H 2, H 2` pair cancelled through a lemma module under `Solution/` at 5
  gates; on `tof_3`, PyZX's twin with its four windows is accepted at
  T-count 19 with 50 gates, an improvement under the default order although
  the original has 45;
- rejected: a cheap circuit behind `sorry` (the axioms); a changed
  `Harness/Task.lean` (before lake runs); a true `equiv` about another
  constant than the cheap `optimized` (the restatement does not typecheck);
  `implemented_by` (the scan); cost functions supplied by the solution under
  the harness's names (the import clashes); `≡ᵤ` claimed on the up-to-phase
  task;
- an equivalent circuit that costs more than the original is accepted as no
  improvement and never becomes the score;
- with the working files broken after three accepted submissions, the final
  judge scored the cheapest copy; with that copy then corrupted, it fell
  back to the next cheapest and said why;
- with the text scan bypassed, an `implemented_by` that makes `#eval` report
  the cost `[0, 0, 0]` is refused by the kernel's confirmation;
- the clock, with a shell script in place of an agent (no model is called):
  one improvement submitted after 13 s, garbage left in `Solution.lean`, a
  sleep past a one-minute budget. The harness stopped it at the deadline
  plus the grace, scored the kept copy, and recorded `timed_out`.

`selftest` covers, without lake: the cost order, the prompt of every task,
the templates, the import rule, the kept copies, and the final judge's
choice among candidates with a stand-in for Lean.

## Not built yet

- Everything the equivalence harness lacks: isolation above all. The
  pristine clone and the kept copies sit beside the workspace under the same
  user account.
- The `core` configuration. `--config core` is passed through to the shared
  setup, which fails at `a9a80ed` for both harnesses: `CORE_MODULES` in
  `agent_harness.py` lacks `Chunk`, which `Semantics.lean` now imports.
  Whether `Chunk` belongs in `core` is a decision about the hypothesis, so it
  is left as found.
- Depth as a cost (it needs a definition in Lean that the kernel evaluates
  cheaply), and any cost that is not a count.
- A playbook section on optimising: which oracles exist and how to call them.
  The prompt names what the machine offers (`./python` with PyZX, `./tzap`,
  `./qasm`) and no technique, by design, and `PLAYBOOK.md` is still the
  prover's guide only.
- A judge that does not elaborate its files next to the agent's modules.
  The restatement, the `#eval` and the confirmation import `Solution`, so
  macros or elaborators defined there could in principle reinterpret the
  judge's syntax; the text scan lists new notation and macro rules for the
  person who reads the diff, and nothing more. The same holds for the
  equivalence harness.
- A held-out ladder, repeated runs, a summary over `opt-results.jsonl`, and
  the comparison of certified against uncertified T-counts that the roadmap
  asks for, as a table.
