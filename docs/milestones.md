# Milestones for the equivalence checker

What counts as a milestone for the AI + Lean equivalence checker, how a
candidate is chosen and measured, and which pairs of the circuit catalogue
are the candidates today (22 September 2026). `ROADMAP.md` defines the goal
this document serves, S: a real circuit pair that the published checkers
cannot decide within the benchmark protocol's limits and that this library
proves. `docs/tool-survey.md` is where the published checkers stop;
`benchmarks/circuits/` is where the pairs come from; `QUEUE.md` holds the
work items each milestone needs.

## Definition

A milestone is a pair of realistic circuits with a named application, made
the way such pairs are made in practice, on which every published checker
fails to *prove* equivalence under a fixed protocol, and for which a
kernel-checked proof exists in this repository. Three words of that
definition carry conditions.

- **"Every published checker fails" is a measurement, not a citation.** The
  protocol is `ROADMAP.md`'s: QCEC (`mqt.qcec`, the default portfolio and the
  alternating DD checker on its own), PyZX (`verify_equality` on the miter),
  quizx (`full_simp` and stabiliser decomposition), Feynman (`feynver`) and
  any newer checker that installs; one hour of wall clock and 16 GB per pair;
  the verdict recorded as proved, refuted, inconclusive, timeout or memory,
  with the tool's version. The survey's published ceilings say where to look
  and are used below as predictions. The record is the run
  (`QUEUE.md`, item 15). `scripts/hard_pair.py ladder` already drives PyZX,
  quizx and QCEC from the harness environment `envs/qcec` under a timeout
  and a memory watchdog; the protocol run reuses that driver on catalogue
  pairs.
- **"Realistic with an application" is a whitelist.** Origin circuits from
  published suites that implement a named primitive: arithmetic for Shor's
  algorithm and elliptic-curve cryptanalysis (adders, multipliers, modular
  arithmetic, the `gf2^k` multipliers), Hamiltonian simulation and quantum
  linear algebra (the `ham15` and Cobble circuits), the QFT, Grover, and
  QEC. Twins made by optimisers people run, at settings they ship: TZAP,
  PyZX phase teleportation and `full_reduce`, the published Nam et al.
  outputs, and Qiskit at optimisation level 3 once the catalogue has it.
  That admits most of tiers 2 to 4 and excludes `hwb`, the peephole twins
  and the constructed pair of `benchmarks/hard_pair/`, which is a synthetic
  existence proof and is recorded as such, not as a milestone.
- **"Prove" is the verb.** Below about 40 qubits random stimuli refute a
  wrong pair cheaply, so a refutation cannot be beyond the tools there, and
  a mutant of a milestone pair is a control, not a milestone. Proving is
  where the tools fail, and a proof at 15 qubits and above already defeats
  the dense unitary (`16 · 4^n` bytes: 68 GB at 16 qubits).

Size tiers are not the criterion. Tier 1 holds both trivial Clifford
preparations and `mod5_4` against `full_reduce`, which is hard by shape and
easy only because five qubits brute-force; tier 4 holds `gf2^256_mult`,
which no tool and no proof reaches, and GHZ on 1000 qubits, which the
tableau decides in seconds. A milestone is chosen by the mechanism the pair
forces and the quantity that defeats each tool, and only then by size.

## What predicts the tools' failure, and our cost

The survey's finding (`docs/tool-survey.md`, section 4.1) is that each
technique has one structural quantity that sets its cost, and that qubit
and gate counts predict little. The quantities that matter for choosing a
pair, with the ceilings the papers report:

| Technique | Governing quantity | Reported ceiling |
|---|---|---|
| Dense unitary, state vectors | `n` | 14 to 15 qubits |
| Decision diagrams (QCEC) | whether the two gate orders line up; distinct amplitudes | compiled RevLib pairs of 22 to 34 qubits exceed 1 h; reported to hang from `gf2^8_mult` (24 qubits) on TZAP output |
| Path sums (Feynman) | path variables, the Hadamards no rule eliminates | out of memory at 508 path variables (`gf2^64_mult`) and 2282 (`hwb8`); `gf2^32_mult` verified in 431 s |
| Stabiliser decomposition (quizx) | non-Clifford gates left after simplification, cost `2^{0.4 t}` | 4 % of 50-qubit random circuits at `T = 50` in five minutes |
| ZX rewriting (PyZX, QCEC's ZX checker) | non-Clifford phases that survive simplification | inconclusive at any size once they survive; `full_reduce` over 1 h on `gf2^64_mult` |
| Clifford tableaux (Stim, CCEC) | none within Clifford | millions of gates; not applicable with a `T` |

None of these is this library's cost. With an aligned pair, a certificate
replays in time linear in the trace, and a window in the CNOT-plus-diagonal
fragment is decided by the phase polynomial in time linear in its gates and
never `2^n` (`benchmarks/scale/README.md`). So the Hadamard count that
exhausts Feynman, the T-count that defeats quizx and the width that defeats
simulation cost us nothing extra, *provided the pair aligns*. What costs us
is the opposite quantity: a twin whose gate order is unrelated to the
original's, which needs the residual mechanism (`QUEUE.md`, item 10), and,
independently of alignment, certificate length (item 3) and a window that
contains a Hadamard (items 4 and 7).

That is the shape of the first milestones: skeleton-preserving twins of
T-heavy, Hadamard-heavy circuits at a width past simulation. The optimiser
did the alignment; the tools cannot use it; we can.

## Candidate milestones from the catalogue

Sizes are the original circuit's, from `benchmarks/circuits/manifest.json`.
The relation is the one `pairs/index.json` records for the twin (`unchecked`
means no numerical oracle could check the pair at that width, so Lean would
be the only checker). The failure column is a prediction from the ceilings
above and is to be replaced by the protocol run's verdicts.

| Pair | Qubits | Gates | H | T | Relation | Predicted tool failure | What we still need |
|---|---:|---:|---:|---:|---|---|---|
| `gf2^16_mult` vs TZAP `-O1` | 48 | 4459 | 1086 | 1792 | `≡ₚ`, unchecked | H past Feynman's memory, T past quizx, width past simulation, QCEC's reported hang | items 7 or 4, item 3 |
| `gf2^32_mult` vs TZAP `-O1` | 96 | 17658 | 4222 | 7168 | `≡ₚ`, unchecked | as above; Feynman verified a `gf2^32` multiplier with 252 path variables, so it may pass here | a linear certificate at this length |
| `gf2^64_mult` vs TZAP `-O1` | 192 | 70075 | 16638 | 28672 | `≡ₚ`, unchecked | Feynman out of memory, PyZX over 1 h, QCEC | compact encoding of the instruction list |
| `mod_adder_1024` vs TZAP, teleport | 28 | 5425 | 1710 | 1995 | `≡ᵤ`, exact | H count; Toffoli arithmetic is Feynman's strong case, so measure first | items 7 or 4, item 3 |
| `cuccaro_128`, `adder_n118` vs teleport, TZAP | 118 to 258 | 1834 to 4353 | 208 to 512 | 728 to 1792 | `≡ᵤ`, `≡ₚ` | width alone; Feynman may pass | item 3 |
| `ham15_high` vs teleport, TZAP | 20 | 6712 | 2106 | 2457 | `≡ᵤ`, exact | H and T density; 20 qubits past the dense unitary | items 7 or 4, item 3 |
| Cobble `hamiltonian_simulation`, `chebyshev` vs TZAP | 14 to 16 | 112554 to 226196 | 31227 to 52419 | 47894 to 99219 | `≡ₚ`, `≡ᵤ` | density defeats DD and ZX at a width the hard-pair ladder already saw QCEC's DD time out at | compact encoding, item 3 |
| Synthesised QFT `q050` vs TZAP | 50 | 1030570 | 471018 | 557027 | `≡ₚ`, unchecked | everything | compact encoding |
| `gf2^8_mult` to `gf2^10_mult` vs Nam heavy, `full_reduce`, Qiskit level 3 | 24 to 30 | 1139 to 1747 | 286 to 438 | 448 to 700 | `≡ᵤ` | no alignment for the DD checker either; Feynman is the one to beat | the residual mechanism, item 10 |
| T-par outputs equal only on clean ancillas (`gf2^6` to `gf2^9`, `tof_10`) | 18 to 27 | 323 to 1419 | 102 to 358 | 119 to 567 | subspace | no published tool has the relation; SliQEC's partial equivalence times out at 20 data qubits | Rung 5 of `ROADMAP.md` |

Three notes on the table.

- **The TZAP twins in `pairs/` do not align.** They were made at `-O2`, which
  keeps the CX/H/X skeleton on 18 of 99 circuits; `-O1` keeps it on 89
  (`benchmarks/circuits/README.md`, "Which TZAP level keeps the skeleton").
  The first three rows need `-O1` twins, made in seconds with
  `CIRCUITEQ_TZAP_ARGS="-O1 --decompose-rz --decompose-cz"` and
  `scripts/circuit_pairs.py probe --twin tzap`. The `-O2` twins stay in the
  catalogue as pairs that do not line up, which the harness wants
  (`QUEUE.md`, item 1); for milestones they belong with the re-synthesised
  row.
- **Hadamard count overestimates path variables.** Feynman eliminates the
  Hadamards inside a Toffoli, which is why it verifies Toffoli-built adders
  at hundreds of qubits and a `gf2^32` multiplier with 252 path variables
  against 4222 Hadamards. The arithmetic rows may therefore be within
  Feynman's reach below `gf2^64`; only the run says.
- **The QCEC claim is second-hand.** That QCEC hangs from `gf2^8_mult`
  upward is reported by TZAP's evaluation of its own output, on one QCEC
  version and configuration. It is the first thing the protocol run should
  test.

## The experiment that orders the ladder

Reversible arithmetic has a permutation unitary, which decision diagrams
represent compactly, and a skeleton-preserving twin keeps the gate order
that QCEC's alternating scheme relies on. So the first run is QCEC 3.10.0
(default portfolio, and the DD checker alone) on `gf2^k_mult` against its
TZAP `-O1` twin and its phase-teleportation twin, for `k` from 4 to 64,
one hour each. Two outcomes:

- **QCEC proves them.** Aligned arithmetic is then a T result, not S, and
  the first milestone moves to the re-synthesised twins (the ninth row) or
  to the Hamiltonian-simulation rows, whose T and H density is what defeats
  decision diagrams. The residual mechanism becomes the first work item.
- **QCEC hangs as reported.** The first S is then within reach of cutting
  at Hadamards (item 7) plus chunked replay (item 3), with no new
  mathematics, at `gf2^16_mult` if Feynman also fails there and at
  `gf2^64_mult` otherwise.

Feynman decides the second question and has to be built (Haskell); until
it is, the run records it as not run rather than as failed.

## How a milestone is determined and recorded

For each whitelisted family and each real twin kind, the protocol runs up
the family's size ladder.

- **The floor** is the smallest size at which every protocol tool fails to
  prove the pair. The milestone is a kernel-checked proof at the floor.
- **The stretch** is the largest size the kernel checks within the same hour
  and 16 GB. It is what the crossover table reports as ours.
- **The order** of milestones is by the mechanism the twin kind requires:
  aligned windows first, then residuals, then a new relation; within a
  mechanism, by floor size. The mechanism rungs of `QUEUE.md` are the work
  items under each milestone, each with its own small held-out pairs, so
  that a miss on the milestone pair can be attributed to one rung.
- **A milestone ships** the pair's hashes (`manifest.json`,
  `pairs/index.json`), the tool logs with versions, the Lean proof and its
  kernel time, and a gate-deleted mutant refuted alongside. Every pair the
  protocol was run on appears in the crossover table, including the ones we
  did not prove, with the failure named (`ROADMAP.md`, Rung 3's acceptance).
- **Hold-out.** A milestone pair has no proof in the repository or its
  history before the run that proves it, and the agent harness's tasks for
  it are held out as `benchmarks/harness/README.md` describes. Nam et al.
  and T-par twins live in the cache only, for the licence reason recorded in
  the catalogue, so a milestone on them is reproducible from one command
  but its twin is not a public fixture.

## What is not a milestone under this definition

- **Clifford-only families** (GHZ, cat states, surface-code cycles, the QEC
  encoders): Stim and CCEC decide them at any size, so a tableau proof is a
  T result. They remain the tableau's regression ladder.
- **Pairs under about 15 qubits**, whatever their gate count: the dense
  unitary proves them. `hwb8` at 12 qubits, which exhausts Feynman, is the
  example.
- **Refutations under about 40 qubits**: random stimuli find them. The
  wrong published output for `qcla_mod_7` at 26 qubits is a refutation task
  for the harness, not a milestone.
- **The constructed pair** of `benchmarks/hard_pair/`: past every installed
  checker from 16 qubits in its own ladder, and certifiable in principle by
  tableau, phase polynomial and a frame-change step, but not a circuit
  anyone compiled for a purpose. It is the existence proof that the
  architecture reaches where the tools do not; the milestones are the
  realistic instances of the same claim.
