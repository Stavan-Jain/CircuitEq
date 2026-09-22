# Queue — what to do next, in order

The working list for this repository: the next pieces of work, each with
enough context to pick it up cold. Items are ordered by priority within a
section; take the top item whose dependencies have landed. When an item
lands, move it to "Done" with its commit hash. Design context is in
`ROADMAP.md` ("Two products, one architecture") and CLAUDE.md ("What we
are optimising for"); the rules for new modules are in the docstrings of
`CircuitEq/Checker.lean` and `CircuitEq/Support.lean`.

Sizes: S is a session, M a few sessions, L a milestone.

## In flight (22 September 2026)

Item 1, the agent harness: a draft is in `scripts/agent_harness.py` and
`benchmarks/harness/` with 21 tasks (ten for development, two of them TZAP
pairs; eleven held out, the 1000-gate pair and ten from the catalogue),
the prompt, the playbook (`PLAYBOOK.md`) and a judge by restatement,
axioms and kernel replay. Three runs so far,
the third proved. The optimisation harness (`scripts/optimizer_harness.py`)
is built on the same pieces and tested by hand, with no agent run yet. The
held-out ladder and the baselines landed on 21 September (`720583d` and
the TZAP follow-up): `benchmarks/circuits/`, 147 real circuits in four
tiers with an exact-or-refuse QASM importer, 390 pairs with the relation
that actually holds (ten imported as held-out tasks), and
`optimization.json` with what PyZX, TZAP, Nam et al. and T-par reach on
every T-bearing circuit. Still open before item 1 is "done": repeated runs
with a summary table, the record of which declarations a proof uses
(`benchmarks/harness/README.md`), and closing the channels through which a
run can learn how its pair was made (item 1). The catalogue's `tzap` twins
are made at `-O2` and mostly do not line up (18 of 99 keep the skeleton,
22 September); they stay that way on purpose, as the kind of pair the
agent has to handle, and item 4 is the tool planned for them.

## Next

1. **Agent harness v0.** The project's bet is that this infrastructure
   lets an agent prove pairs it otherwise could not, and nothing measures
   it: every alignment so far was found by a person or by the diff script
   in `scripts/tcount_survey.py`. Build the instrument now, so that each
   later item is judged by what it moves, and rerun it as the library
   grows. `scripts/agent_harness.py` takes a task and an agent command
   (Claude Code headless first) and: copies the repository at a pinned
   commit into a scratch directory, without `.git`; holds the answer out
   (deletes the pair's module under `CircuitEq/Benchmarks/`, its import
   and its `benchmarks/<name>/README.md`; the tableau's regression tests
   in `CircuitEqTest/` embed the `rep3` and Steane pairs with proofs, so
   those two are development tasks at best, and a test task is a pair that
   appears nowhere in the repository); writes a statement file with the two
   circuit `def`s and `theorem … : original ≡ᵤ optimized := by sorry`
   (the relation is per task: `≡ᵤ`, `≡ₚ`, `≡ₛ`, or a negation for a
   mutant); gives the agent one checked-in prompt
   (`benchmarks/harness/PROMPT.md`), the lean-lsp tools and the benchmark
   protocol's limits (one hour, 16 GB); then judges. The agent may write
   any Lean it likes, new lemmas, checkers and step kinds included. The
   judge for v0 is a person reading the diff: no existing file changed
   (the trusted `Semantics.lean`, the circuit `def`s and the
   statement above all), `lake build` passes and `#print axioms` shows
   the standard three. The axiom check alone is not enough: on this
   toolchain `set_option debug.skipKernelTC true` lets a false
   `decide +kernel` through with a clean axiom report, so the review also
   looks for `debug.` options until the CI guard against them lands. An
   automated judge that replays the solution through the kernel is
   deferred (see "Later"). Record outcome (proved, refuted, no
   certificate), wall time, kernel time, tokens, and which library
   declarations the proof uses (the roadmap's flywheel record).
   Tasks v0, ordered by gates times width: the five promoted pairs, the
   survey's eleven circuits under both pipelines, and one gate-deleted
   mutant of each. Two configurations, the full library and the semantics
   with its decision procedures alone (up to `Decide.lean`), since their difference is the
   hypothesis. An optimiser track follows item 2: the input is one
   circuit, the answer is `c'` with a proof of `c ≡ᵤ c'` and
   `tCount c' = k`, and `k` is reported against the uncertified T-counts
   of PyZX and TZAP, which the agent may call. Acceptance: the v0 table
   is checked in under `benchmarks/harness/` with a written failure mode
   for every miss; a run is reproducible from commit, prompt and task;
   submissions that use `native_decide`, `sorry`, `debug.skipKernelTC` or
   an edited statement are rejected. S to M. Depends on nothing; the
   optimiser track on item 2. Since this was written (21 September 2026):
   the harness, its automated judge (restatement, axioms, kernel replay;
   the `debug.*` guard is in CI) and the optimiser track exist in
   `benchmarks/harness/`, and the held-out ladder is the circuit
   catalogue; the task set is the one recorded there, not the one planned
   above. Still open: repeated runs with a summary table and the
   declaration record ("In flight"), and a blind harness. The agent is the
   checker and must learn nothing about a pair but its two circuits. The
   workspace already drops the task's name and metadata, `benchmarks/`,
   the design documents and the history, but three channels remain.
   (a) The run is offered `./tzap`, and PyZX in `./python`, and rerunning
   the tool that made a twin on `original` reproduces `optimized` (TZAP's
   output was the same on every run measured), so the producer and its
   level can be recovered by experiment. (b) The playbook, the run's
   `CLAUDE.md`, sorts its advice by producer (entry 5, "phase folding,
   phase teleportation, peephole passes"; entry 8, "PyZX and TZAP drop
   scalars"). (c) Each tool's output has a style of its own: gate order,
   how rotations and `CZ` come back decomposed. Levers: held-out tasks are
   never made by a tool the run is offered (or the run is offered none);
   both circuits of every task are put into one canonical order of
   commuting gates before the agent sees them, which keeps the relation
   and blurs (c), though a diff after the agent's own reordering still
   matches; the playbook is phrased by what the agent can see in the pair.
   Acceptance: the harness self-test fails when a held-out task's
   `optimized` is reproduced, up to the order of commuting gates, by a tool
   the run is offered at any of its levels; no playbook entry names a
   tool. Changing what the prompt offers changes the instrument: bump
   `HARNESS_VERSION`.

2. **Cost functions in Lean.** The roadmap's architecture says costs are
   computed in Lean so that "this circuit has T-count 19" is a checked
   claim; nothing exists yet, and the optimiser cannot state its result
   without it. A module `CircuitEq/Cost.lean` importing only `Semantics`
   (and imported by the umbrella): `tCount` (`T` and `Tdg`), `cxCount`,
   `gateCount : Circuit n → ℕ`, with `tCount_append` there and
   `tCount_rename` beside `rename` in `Embedding.lean` (and the same for
   the others), so that costs compose under `in_context`, windows and
   `rename`; depth, by per-wire time stamps, only when a benchmark needs
   it. The optimiser's statement shape is `c ≡ᵤ c' ∧ tCount c' = k`, the
   second half pure `Nat` evaluation. Acceptance: the T-counts the README
   quotes for `tof_3` (21 to 19) and `barenco_tof_3` (28 to 24) are
   theorems beside the equivalence in their benchmark modules (extend the
   convention in `CLAUDE.md`, which today allows only the two `def`s and
   the equivalence), and `scripts/check_pyzx_benchmarks.py` cross-checks
   them against PyZX's own count. S. Depends on nothing.

3. **Replay memory.** `cuccaro_4`'s certificate (155 gates, 8 windows)
   is killed at 4.6 GB while the same windows pass on `cuccaro_3`, and a
   128-gate move-only replay peaks at 1.9 GB: the kernel's `whnf` cache
   retains every intermediate instruction list for the whole declaration.
   The two other victims of that retention are done (see "Done": the
   chunked basis decide and the chunked tableau, `CircuitEq/Chunk.lean`);
   replay is what is left. Levers, in order: a compact `Nat` (or `String`)
   encoding of the instruction list decoded by the kernel (the canonical
   phase polynomial showed what this buys: packing the row table into one
   `Nat` took a CNOT from about 1.5 MB of retained `List.set` terms to a
   shift and an xor); chunked replay, one theorem per segment of the
   trace composed by `Equivalent.trans`, in a file with
   `set_option Elab.async false`; cursor-based steps (item 6).
   Acceptance: `cuccaro_4` / teleport checks under 2 GB. M. Depends on
   nothing.

4. **Path sums of the pair (phase polynomials with Hadamard variables).**
   The tool for pairs that do not line up (`ROADMAP.md`, "The pair as one
   circuit"), which is most real optimiser output: TZAP's `-O2` twins keep
   the CX/H/X skeleton on 18 of the catalogue's 99 circuits
   (`benchmarks/circuits/README.md`, "Which TZAP level keeps the
   skeleton"), and at the median a diff matches under half of the gates
   of the published Nam et al. and PyZX outputs and under a tenth of
   `full_reduce`'s. The agent is not told which kind of pair it holds, so
   this cannot be a tool for one producer. Represent `a ++ inverse b` as a path sum: extend `PhasePoly`
   so that an `H` on a wire introduces a fresh variable instead of ending
   the fragment; the linear part ranges over input and Hadamard variables,
   the phase polynomial too, and the semantic invariant becomes a
   superposition over Hadamard outcomes with the `(−1)^{p·h}/√2` factor of
   `applyOne H`. The dense planes of `PhasePoly` do not survive this (the
   triple plane would be `C(n + h, 3)` bits for `h` Hadamards), so the
   phase polynomial becomes a sparse list of monomials. Then, as step kinds
   of the certificate language with their cases in `replayStep_sound`:
   Amy's reduction rules (drop a variable that does not occur; the `HH`
   rule, which sums out a variable that occurs only as `(−1)^{y·Q}` and
   substitutes for a variable of `Q`; the `ω` rule), each proved to
   preserve the denotation, and a closing check that
   the reduced sum is the identity, or `ω ^ k` times it for `≡ₚ[k]`. The
   search for the rewrites is untrusted: a Python mirror beside
   `scripts/certificate.py`, or Feynman's verifier as an oracle, emits the
   trace. Two things fall out. The theorem for aligned pairs (same CX/H/X
   skeleton and same phase map give `≡ᵤ`) is the case where the reduction
   is trivial, a fast path. And on an unequal pair, one amplitude of the
   reduced sum, a sum over the variables left, differs from the identity's:
   a refutation witness, as a step kind of item 11. The representation is
   the one TZAP (arXiv 2605.13929) and Feynman's affine analysis compute,
   and it is Rung 8's normaliser and Rung 3's latent-algebra tool. Acceptance, all
   on pairs that do not line up: `tof_3` against its `-O2` TZAP output
   (harness task `tof_3_tzap`) by one replay; the published pair
   `feynman_vbe_adder_3__pyzx_published` (10 qubits) and a TZAP `-O2`
   pair of a few thousand gates in minutes of kernel time; `tof_3_mut1`
   and one mutant past a basis decide refuted by a witness. M to L.
   Depends on nothing; the refutation half on item 11.

5. **TZAP as a pipeline.** Build `tzap` from
   https://github.com/qqq-wisc/tzap, add a `tzap` pipeline to
   `scripts/check_pyzx_benchmarks.py` and the survey script, and add pairs
   from the Feynman suite (`gf2^k_mult`, `mod_adder`, `barenco_tof`,
   `hwb`) at the sizes the kernel reaches. Record the level with every
   pair: at `-O1` TZAP's output keeps the skeleton up to cancelled pairs
   and `CancelGates`' one-wire Hadamard reductions (`H S H` to
   `S† H S†`, `H Z H` to `X`), at `-O2` and `-O3` it does not
   (`benchmarks/circuits/README.md`, "Which TZAP level keeps the
   skeleton"), and an agent is told neither. Acceptance: the
   fixture script reproduces TZAP output byte for byte and the Lean lists
   match. S for the script; certification beyond `H`-free regions depends
   on item 4. Partly done on 21 September 2026 in `benchmarks/circuits/`:
   TZAP 0.6.1 is a twin kind of `scripts/circuit_pairs.py`, run on every
   T-bearing circuit of the catalogue, tier 4 included, with the relation
   that holds recorded per pair (`pairs/index.json`) and its T-counts in
   `optimization.json`. Still open: the `tzap` pipeline of
   `check_pyzx_benchmarks.py` and the byte-for-byte fixture.

6. **Linear certificates.** Make traces cursor-based (a position carried
   along, not re-indexed into a `List` per step) so replay is linear in
   trace plus circuit length; add a `template` step kind that applies a
   registered lemma proved for all `n` at a concrete `n`, with its case in
   the Python mirror `scripts/certificate.py`.
   Acceptance: kernel time on `Tof3.lean` alignment linear in gates;
   `layer_cnotNetwork_hLayer` usable as a step. M. Depends on item 3.

7. **Survey v1: cut at Hadamards.** Replace diff-sized windows with the
   largest contiguous `H`-free regions (pulled together by commutations)
   checked by the phase-polynomial checker, keep the basis decide for the
   residue near Hadamards, add the `tzap` pipeline, rerun, and record
   which pairs still need the residual pattern. The survey's own analysis
   says where this lands: every wide window of the structured teleport
   pairs is one or two CNOT-plus-diagonal segments around one interior
   Hadamard, so `tof_3`, `tof_4`, `tof_5`, the adders and `mod5_4` become
   proofs with no basis decide wider than one wire, and the recurring
   library gap (`[CX 4 3, CZ 3 4] ≡ᵤ [Sdg 3, CX 4 3, S 4, S 3]`, a `CZ`
   through a control-only block) is a phase-polynomial identity. Cutting
   at Hadamards needs the two circuits' Hadamards to correspond, which
   holds for phase teleportation and TZAP at `-O1`, not for the
   catalogue's `-O2` twins; those are item 4's. S. Depends on item 5 for
   `tzap`; nothing else.

8. **Phase-polynomial follow-ups.** The affine `X` extension (a constant
   bit per row); `ofNF` resynthesis with `nf (ofNF x) = some x`, which
   turns any untrusted synthesis heuristic into a certified T-count
   optimiser for the fragment (completeness has landed, so the form is a
   canonical target). Also the remaining kernel cost: the triple plane
   is one `C(n, 3)`-bit `Nat`, 164 KB at 200 wires, and every gate that
   changes it copies it, which is the 5.3 GB of the 300-wire CCZ rung
   (`benchmarks/scale/`). A plane split by top wire, in a structure the
   kernel can update without walking a list (a binary trie of `Nat`s), is
   the lever past a few hundred wires. M. Depends on nothing; resynthesis
   is the first
   optimiser deliverable.

9. **A column-packed tableau.** The tableau walks the circuit once per
   generator, `2n · gates` steps at 0.2 to 0.3 ms each: 7 minutes for the
   80-qubit random rung (`benchmarks/scale/`). Keep the whole tableau as two
   `Nat` bit matrices (bit `2n·j + g` for wire `j`, generator `g`) and two phase
   planes, so a gate is a few shifts and xors on all generators at once and the
   cost is `gates`: an estimated factor of sixty at 80 qubits, and no chunking.
   Soundness by decoding: the row `g` of the packed state after a gate is
   `Gate1.conj` of the row before, so the final state gives `Tableau.ConjAgree`
   and `Tableau.equivalentUpToScalar_of_conjAgree` applies unchanged.
   Acceptance: the 80-qubit rung in seconds, 500 structured qubits. M. Depends
   on nothing.

9a. **The 19-origin Clifford run.** Every QECUnitaryCircuits origin against
   its PyZX `full_reduce` twin by the tableau checker (`≡ₛ`), the
   gate-deleted mutants refuted with a Pauli witness, and the table
   published with kernel times: this is Rung 1's acceptance test for that
   family and Rung 4's first evidence. S to M. Depends on nothing.

10. **Residual pattern.** Cut points where one circuit's prefix times the
    inverse of the other's is a Clifford (tableau) or a diagonal (phase
    polynomial), proved preserved step by step, as a certificate step kind.
    First target: `tof_3` against `full_reduce` (T-count 15), which has no
    window alignment. L. Depends on item 4.

11. **Refutation certificates.** Step kinds that prove `¬ (a ≡ᵤ b)`: a
    basis vector on which the evaluators differ, a Pauli whose images under
    the two tableaux differ. `phasePolyRefutes` already does this for the
    CNOT-plus-diagonal fragment by completeness (`PhasePoly.refutes_sound`);
    the step kinds make it composable. Needed for mutants and for the
    survey's negative results. S. Depends on item 3.

12. **Rung 2 conformance.** A Qiskit statevector check of
    `lean_instructions` on the benchmark files and a few hundred random
    circuits (the `rz` global-phase trap), run in CI. S. Depends on
    nothing.

13. **The scalar replay.** Done for a global phase (see "Done":
    `replayPhase`, `circuit_windows` on `≡ₚ` goals), which is what pairs
    equal only up to a phase needed. What is left is the `≡ₛ` half, so that
    `tableauChecker` can justify windows and, later, residuals: a
    `ScalarCheckerTable`, a third interpretation of `window` whose
    soundness uses `EquivalentUpToScalar.append` and
    `EquivalentUpToScalar.rename` (landed with the phase work), a `cons`
    lemma for `≡ₛ` (one line, for `rewriteAt_rel`), and
    `replayScalar_sound : … → c ≡ₛ c'`. A unit scalar cannot be accumulated
    as data the way an exponent in `Fin 8` is, so this replay concludes the
    existential and names nothing; follow `replayUpToPhase`. S. Depends on
    nothing.

14. **A block-theorem step.** A step kind that applies a registered lemma
    such as `layer_cnotNetwork_hLayer` at a position, so the Steane proof
    and the Python mirror no longer need a `calc` around the certificate;
    this is the first form of the template step of item 6. S. Depends on
    nothing.

15. *(done, folded into item 3)* The seven-qubit decide was measured on
    an idle machine: killed by a 6 GB watchdog after 20 s at 6.9 GB and
    growing, so memory is the limit and chunked evaluation is the lever.

## Later

- A stronger judge for the agent harness. It now restates the theorem in a
  file it owns, checks the axioms and replays the solution through the
  kernel with the toolchain's `leanchecker`. Left: judging in a pristine
  checkout that receives only the agent's new files, isolation of the
  agent (it has a shell under the user's account), and an independent
  checker (SafeVerify, or `leanprover/comparator` on the Linux CI).
- Hierarchical circuits (named blocks, congruence) and compact encodings
  decoded by the kernel, before any circuit above a few thousand gates.
- The wire-index decision (`Fin n` versus `ℕ` with well-formedness) before
  Rung 6 template work; then `cnotLadder n`, Toffoli as a macro, adders.
- Routing as `rename` by a permutation; ancilla subspaces as a side
  condition on congruence (Rung 5, only as Rung 6 needs it).
- `≡ₛ → ≡ₚ` for Clifford circuits (units and the prime over 2 in `ℤ[ω]`).
  It now has a customer: with it, and one amplitude of each side evaluated
  to name the exponent, the tableau becomes a `PhaseFinder` and joins
  `defaultPhaseFinders`, so a wide Clifford window of a pair stated on
  `≡ₚ[k]` is decided in `O(n)` per gate instead of `2 ^ k`.
- The uniqueness of a named phase: `a ≡ₚ[j] b → a ≡ₚ[k] b → j = k` needs
  `denote b ≠ 0`, which fails for a circuit with a degenerate `CX c c`
  (`[CX c c, Z c, H c, CX c c]` denotes zero); state it for circuits whose
  CNOTs have distinct wires, by `denote_inverse_denote`.
- `Zeta8.toComplex`, unitarity of every gate, the QECLean bridge.
- Dyadic normalisation tuning once the ring's measurements are in.
- Rung 8: the phase-polynomial form with phases in `ZMod (2 ^ m)` (the
  degree bound becomes `m`, so the planes grow with it).
- Kernel engineering: recursion depth on long lists, chunked replay.

## Done

- `83cc1d7` Composition up to
  a global phase, because PyZX and TZAP preserve a circuit only up to one.
  `EquivalentWithPhase` (`a ≡ₚ[k] b`, `k : Fin 8`) under `≡ₚ`, with the
  algebra of both (`refl`, `symm`, `trans`, `append`, `cons`,
  `in_context`), `Trans` instances so that one `calc` mixes `≡ᵤ`, `≡ₚ[k]`
  and `≡ₚ`, the locality theorem for a phase (proved once for any scalar,
  so `≡ₛ` has `rename` too), `checkEquivWithPhase` / `findPhase` and the
  `Decidable` instance that names a window's phase. `PhaseFinder`,
  `replayPhase` and `replayPhase_sound` (the same `Step`s; the kernel adds
  the windows' exponents up and the theorem names the total),
  `circuit_simp` and `circuit_windows` on `≡ₚ` and `≡ₚ[k]` goals, the
  Python mirror's `replay_phase`. `phaseGadget k i` (`(S H)³ = ω`) and
  `a ≡ₚ[k] b ↔ a ≡ᵤ b ++ phaseGadget k i`. Phase replay of `tof_3`'s
  trace: 0.19 s of kernel time against 0.16 s exact.
- `16a1a02` Kernel replay in CI. The axiom check could not see a false
  `decide +kernel` theorem sealed behind `debug.skipKernelTC` (no axioms,
  no error); CI now replays the built `.olean` files with the toolchain's
  `leanchecker` on one thread (28 s, 0.33 GB here; ten threads die at
  26 GB), asserts on every run that the replay rejects the repro in
  `scripts/SkipKernelTCFixture.lean`, and runs
  `scripts/check_debug_options.py` as an early, unsound text guard.
- `5178a32` Phase gates cost their parity's weight, not the register
  width: `sparseFold` (set bits by `gcd` and a checked population count)
  behind `maskFold`, and `Lanes.addOnz`; the CCZ-network family added to
  the scale test and certified to 300 wires and 10200 gates in 10 s of
  kernel time, the 100-wire rung from 40 s at 6.8 GB to 7 s at 2.7 GB;
  the 161- and 241-qubit surface-code rungs certified. The pass-through
  chain trap recorded in CLAUDE.md.
- `ec9976c` Chunked evaluation (`CircuitEq/Chunk.lean`): `AllBelow`
  assembles a check proved one index range per declaration;
  `checkEquivAt` / `equivalent_of_allBelow` (and the `≡ₚ` form) for the
  basis decide, `tableauCheckGen` / `tableau_sound_of_allBelow` for the
  tableau, emitters in `scripts/`. The seven-qubit `SteanePlus` decide
  finishes (78 s, 1.98 GB); the 40- and 80-qubit Clifford rungs certify
  (39 s at 2.9 GB, 7 min at 4.0 GB); structured Clifford families to 200
  qubits in seconds. Needs `set_option Elab.async false` in the file.
- `86a8b99` Canonical phase polynomials: `PhasePoly` stores the
  multilinear polynomial over `ℤ/8` (degree at most three) as `Nat` bit
  planes indexed in the combinatorial number system, with packed rows;
  soundness redone, completeness proved (`PhasePoly.complete`), the
  refuter `phasePolyRefutes` exported, the 20-, 40- and 80-qubit CNOT+T
  rungs of the scale test certified and their mutants refuted.
- `7641f8e` (merged `90ca69c`) T-count survey: eleven circuits, two
  pipelines, scripted alignment, `barenco_tof_3` promoted; rerun of the
  width-blocked pairs on the dyadic evaluator (`tof_4`, `cuccaro_2`,
  `cuccaro_3` now check in 5 to 9 s).
- `d134d7e` `phasePolyChecker` registered at index 0 of the certificate
  table, with `evalChecker` as fallback.
- `a163ea5` (merged `fde3773`) Certificate language: `Step`, `replay`,
  `replay_sound`, tactics emitting traces, `scripts/certificate.py`.
- `f29e999` (merged `ffa5522`) Gcd-free `Dyadic8` closure evaluator behind
  the decision instances; three-qubit window 2.66 s to 0.09 s.
- `b90aac9` (merged `fa378fd`) Clifford tableau checker with soundness to
  `≡ₛ`, witness, the 15-qubit Reed–Muller benchmark.
- `2768c71` Phase-polynomial normal form and checker (CNOT plus diagonal).
- `321e631` Checker interface, bitmask wire supports, `≡ₛ`.
- `bc811d0` Rewriting toolkit, `circuit_windows`, locality theorem,
  materialised evaluator, three PyZX benchmark pairs.
