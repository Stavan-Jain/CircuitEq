# The prompt of the equivalence-checking harness

This is the one prompt every run gets. It is part of the harness, so it stays
fixed while the library grows: it says what the goal is, what counts, the
rules and the budget, and nothing about which tools exist or how to use them.
That lives in `PLAYBOOK.md`, which is versioned with the library and installed
as the run's `CLAUDE.md`. Changing this file changes the harness; bump
`HARNESS_VERSION` in `scripts/agent_harness.py` when you do.

Slots filled by the harness: `{relation_clause}`, `{budget_minutes}`,
`{memory_limit_gb}`, `{python_clause}` (the rules that name what the machine
offers beside the library: `./python`, when the harness found a Python with
`numpy` and `pyzx`, which the library's scripts import; `./qasm`, the
harness's exact converter between Lean lists and OpenQASM 2; `./tzap`, when
TZAP is installed, as an untrusted oracle) and `{subagent_clause}` (empty
unless subagents are enabled).
Nothing in the prompt or the workspace says which task this is.

<!-- prompt begins -->
# Task

`Harness/Task.lean` defines two quantum circuits over the Clifford+T gate
set, `original` and `optimized`. The second is claimed to be
{relation_clause} to the first. The claim may be wrong.

Decide it with a Lean proof. `Solution.lean` states the claim as the theorem
`equiv` and its negation as `not_equiv`; prove exactly one of them. The
project instructions (`CLAUDE.md`) describe the library you are working in.

## What counts

Run `./submit equiv` or `./submit not_equiv`. It builds your solution, checks
your theorem against the harness's own statement of the claim, replays your
modules through the Lean kernel, and prints `ACCEPT` or `REJECT` with the
reason. It costs about your proof's checking time twice, so leave room for it. The run is scored by the same check
after you stop. When it prints `ACCEPT` you are done: stop.

## Rules

- Your proof goes in `Solution.lean`. You may add lemmas there and new Lean
  modules under `Solution/`, imported from `Solution.lean`. Do not modify or
  delete any other file that exists now, `Harness/Task.lean` above all; a run
  that does is rejected.
- The proof must be checked by the Lean kernel and may depend only on the
  axioms `propext`, `Classical.choice` and `Quot.sound`. So: no `sorry` under
  your theorem, no `native_decide`, no new `axiom`, no `debug.*` option (in
  particular not `debug.skipKernelTC`), no other way of taking the kernel or
  the compiler on trust. A person reads the diff of every run.
- Work inside this directory only, and do not use the network. Never run
  `lake update` or `lake exe cache get`; everything you need is built.
- Run one `lake` command at a time, and never while the Lean language server
  tools are building.
- Other people's Lean processes, and the harness that runs you, share this
  machine and your user account. Stop a command you started with the task
  tools. Never `kill`, `pkill` or `killall` by name, or by a process id you
  did not start yourself.
- A Lean process that uses more than {memory_limit_gb} GB of memory is killed.
  A kernel computation over a whole register of more than a few qubits will
  hit that limit; the project instructions say what scales instead.
{python_clause}
## Budget

You have {budget_minutes} minutes of wall-clock time. `./time-left` prints
what remains. At the deadline the run is stopped and whatever is in
`Solution.lean` is judged. A file that does not build, or still has a
`sorry`, is recorded as "no certificate", the same as the untouched stub:
there is no penalty for a half-finished attempt, so use the whole budget and
do not spend it restoring the stub. If you conclude that you cannot decide the
claim, say so plainly and stop; that too is "no certificate", an honest
result. Only breaking a rule above is worse.
{subagent_clause}
