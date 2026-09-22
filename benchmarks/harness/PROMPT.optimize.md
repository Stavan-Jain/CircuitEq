# The prompt of the optimisation harness

This is the one prompt every optimisation run gets, the counterpart of
`PROMPT.md`. It is part of the harness, so it stays fixed while the library
grows: it says what the goal is, what counts, the rules and the budget, and
nothing about which tools exist or how to use them. That lives in
`PLAYBOOK.md`, which is versioned with the library and installed as the run's
`CLAUDE.md`. Changing this file changes the harness; bump
`OPT_HARNESS_VERSION` in `scripts/optimizer_harness.py` when you do.

Slots filled by the harness: `{relation_clause}`, `{cost_clause}` (the cost
functions of the task's `cost_order` in words, and how two costs compare),
`{original_cost}` (what `original` costs, in the same words),
`{budget_minutes}`, `{memory_limit_gb}`, and `{python_clause}` and
`{subagent_clause}` exactly as in `PROMPT.md`. Nothing in the prompt or the
workspace says which task this is.

<!-- prompt begins -->
# Task

`Harness/Task.lean` defines a quantum circuit over the Clifford+T gate set,
`original`. Find a cheaper circuit that does the same thing, and prove in
Lean that it does.

`Solution.lean` defines `optimized` and states the theorem `equiv`:
`optimized` is {relation_clause} to `original`. Replace `optimized` by your
circuit and keep `equiv` proved. The project instructions (`CLAUDE.md`)
describe the library you are working in.

## What counts

{cost_clause}

`Harness/Cost.lean` defines these functions. The harness measures them on
your `optimized`; you do not report a cost. `original` costs
{original_cost}.

The proof is mandatory. Only a circuit with a kernel-checked proof of `equiv`
is scored; a circuit without one is worth nothing, however cheap. You may
find candidates any way you like, external optimisers included: they are
untrusted, and whatever you submit must be proved here.

Run `./submit`. It builds your solution, checks your theorem against the
harness's own statement of the claim, replays your modules through the Lean
kernel, measures the cost of `optimized`, and prints `ACCEPT` with the cost
and whether it improves on your best so far, or `REJECT` with the reason. It
costs about your proof's checking time twice, so leave room for it. Every
accepted submission is kept, and the run is scored by the cheapest of them,
checked again by the same judge after you stop. So submit each improvement
as soon as it is proved, then go on: a later attempt that fails costs
nothing. As it stands, `Solution.lean` is accepted at the cost of `original`.

## Rules

- Your circuit and its proof go in `Solution.lean`. You may add lemmas there
  and new Lean modules under `Solution/`, imported from `Solution.lean`; Lean
  code anywhere else is not part of a submission. Do not modify or delete any
  other file that exists now, `Harness/Task.lean` and `Harness/Cost.lean`
  above all; a submission made while one is changed is rejected.
- `optimized` must stay a `Circuit` on the same qubits, and `equiv` must keep
  its statement. The harness evaluates `optimized` to measure it and has the
  kernel confirm the numbers, so give it as a list of gates, or as something
  that evaluates to one quickly.
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
what remains. At the deadline the run is stopped. Your score is the cheapest
submission that was accepted, and whatever `Solution.lean` holds at the
deadline is judged once more as a last candidate: an improvement you had no
time to submit still counts if it passes, and working files that do not
build cost you nothing. Do not rely on it: submit as soon as you have an
improvement, since a submission takes about your proof's checking time
twice. If you
conclude that you cannot improve further, say so plainly and stop: your best
accepted submission stands, and with none the score is the cost of
`original`.
{subagent_clause}
