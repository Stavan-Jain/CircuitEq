# Queue — what to do next, in order

The working list for this repository: the next pieces of work, each with
enough context to pick it up cold. Items are ordered by priority within a
section; take the top item whose dependencies have landed. When an item
lands, move it to "Done" with its commit hash. Design context is in
`ROADMAP.md` ("Two products, one architecture") and CLAUDE.md ("What we
are optimising for"); the rules for new modules are in the docstrings of
`CircuitEq/Checker.lean` and `CircuitEq/Support.lean`.

Sizes: S is a session, M a few sessions, L a milestone.

## In flight (16 September 2026)

Nothing. All five parallel branches are merged (see "Done").

## Next

1. **Replay memory.** `cuccaro_4`'s certificate (155 gates, 8 windows)
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
   `set_option Elab.async false`; cursor-based steps (item 4).
   Acceptance: `cuccaro_4` / teleport checks under 2 GB. M. Depends on
   nothing.

2. **Phase polynomials with Hadamard variables (path-sum form).** Extend
   `PhasePoly` so that an `H` on a wire introduces a fresh variable (bit
   `n + j` of the masks) instead of ending the fragment: the linear part
   ranges over initial and Hadamard variables, the phase polynomial too,
   and the semantic invariant becomes a superposition over Hadamard
   outcomes with the `(−1)^{p·h}/√2` factor of `applyOne H`. Then prove
   the theorem that certifies phase-folding output directly: two circuits
   with the same CX/H/X skeleton and the same phase map are `≡ᵤ` (no
   canonical form needed). This is what TZAP (arXiv 2605.13929, phase
   folding in linear time with a randomised parity analysis, no
   certificate) and Feynman's affine analysis compute; it is also Rung 8's
   normaliser and Rung 3's latent-algebra tool. Acceptance: `tof_3` against
   its TZAP output certified in one check; a Feynman-suite circuit of a
   few thousand gates certified in minutes of kernel time. M. Depends on
   nothing.

3. **TZAP as a pipeline.** Build `tzap` from
   https://github.com/qqq-wisc/tzap, add a `tzap` pipeline to
   `scripts/check_pyzx_benchmarks.py` and the survey script, and add pairs
   from the Feynman suite (`gf2^k_mult`, `mod_adder`, `barenco_tof`,
   `hwb`) at the sizes the kernel reaches. TZAP output keeps the skeleton
   (it only deletes rotations, edits angles, and cancels `XX`/`HH`
   pairs), so its pairs are alignable by construction. Acceptance: the
   fixture script reproduces TZAP output byte for byte and the Lean lists
   match. S for the script; certification beyond `H`-free regions depends
   on item 2.

4. **Linear certificates.** Make traces cursor-based (a position carried
   along, not re-indexed into a `List` per step) so replay is linear in
   trace plus circuit length; add a `template` step kind that applies a
   registered lemma proved for all `n` at a concrete `n`; add the Python
   mirror `scripts/certificate.py` if the in-flight branch did not.
   Acceptance: kernel time on `Tof3.lean` alignment linear in gates;
   `layer_cnotNetwork_hLayer` usable as a step. M. Depends on item 1.

5. **Survey v1: cut at Hadamards.** Replace diff-sized windows with the
   largest contiguous `H`-free regions (pulled together by commutations)
   checked by the phase-polynomial checker, keep the basis decide for the
   residue near Hadamards, add the `tzap` pipeline, rerun, and record
   which pairs still need the residual pattern. The survey's own analysis
   says where this lands: every wide window of the structured teleport
   pairs is one or two CNOT-plus-diagonal segments around one interior
   Hadamard, so `tof_3`, `tof_4`, `tof_5`, the adders and `mod5_4` become
   proofs with no basis decide wider than one wire, and the recurring
   library gap (`[CX 4 3, CZ 3 4] ≡ᵤ [Sdg 3, CX 4 3, S 4, S 3]`, a `CZ`
   through a control-only block) is a phase-polynomial identity. S.
   Depends on item 3 for `tzap`; nothing else.

6. **Phase-polynomial follow-ups.** The affine `X` extension (a constant
   bit per row); `ofNF` resynthesis with `nf (ofNF x) = some x`, which
   turns any untrusted synthesis heuristic into a certified T-count
   optimiser for the fragment (completeness has landed, so the form is a
   canonical target). Also the remaining kernel cost: a phase gate on a
   parity of weight `w` costs `O(w)` shift-and-or steps on `C(n, 3)`-bit
   planes, about 10 ms and 2.5 MB of retained terms at 80 wires, so the
   80-qubit rung is 271 such gates; a bounded-width or sparse
   representation of the triple plane is the next lever if wider
   registers matter. M. Depends on nothing; resynthesis is the first
   optimiser deliverable.

7. **A column-packed tableau.** The tableau walks the circuit once per
   generator, `2n · gates` steps at 0.2 to 0.3 ms each: 7 minutes for the
   80-qubit random rung (`benchmarks/scale/`). Keep the whole tableau as
   two `Nat` bit matrices (bit `2n·j + g` for wire `j`, generator `g`) and
   two phase planes, so a gate is a few shifts and xors on all generators
   at once and the cost is `gates`: an estimated factor of sixty at 80
   qubits, and no chunking. Soundness by decoding: the row `g` of the
   packed state after a gate is `Gate1.conj` of the row before, so the
   final state gives `ConjAgree` and `equivalentUpToScalar_of_conjAgree`
   applies unchanged. Acceptance: the 80-qubit rung in seconds, 500
   structured qubits. M. Depends on nothing.

7a. **The 19-origin Clifford run.** Every QECUnitaryCircuits origin against
   its PyZX `full_reduce` twin by the tableau checker (`≡ₛ`), the
   gate-deleted mutants refuted with a Pauli witness, and the table
   published with kernel times: this is Rung 1's acceptance test for that
   family and Rung 4's first evidence. S to M. Depends on the tableau
   branch.

8. **Residual pattern.** Cut points where one circuit's prefix times the
   inverse of the other's is a Clifford (tableau) or a diagonal (phase
   polynomial), proved preserved step by step, as a certificate step kind.
   First target: `tof_3` against `full_reduce` (T-count 15), which has no
   window alignment. L. Depends on the tableau branch and item 2.

9. **Refutation certificates.** Step kinds that prove `¬ (a ≡ᵤ b)`: a
   basis vector on which the evaluators differ, a Pauli whose images under
   the two tableaux differ. `phasePolyRefutes` already does this for the
   CNOT-plus-diagonal fragment by completeness (`PhasePoly.refutes_sound`);
   the step kinds make it composable. Needed for mutants and for the
   survey's negative results. S. Depends on item 1.

10. **Rung 2 conformance.** A Qiskit statevector check of
    `lean_instructions` on the benchmark files and a few hundred random
    circuits (the `rz` global-phase trap), run in CI. S. Depends on
    nothing.

11. **The scalar replay.** A `ScalarCheckerTable`, a window step whose
    soundness uses `EquivalentUpToScalar.append` and a rename lemma for
    `≡ₛ`, and `replayₛ_sound : … → c ≡ₛ c'`, so that `tableauChecker` can
    justify windows and, later, residuals, and so that pairs equal only up
    to a global phase (three of the survey's random pairs) can be stated
    at all by the window pattern. S to M. Depends on nothing.

12. **A block-theorem step.** A step kind that applies a registered lemma
    such as `layer_cnotNetwork_hLayer` at a position, so the Steane proof
    and the Python mirror no longer need a `calc` around the certificate;
    this is the first form of the template step of item 4. S. Depends on
    nothing.

13. *(done, folded into item 1)* The seven-qubit decide was measured on
    an idle machine: killed by a 6 GB watchdog after 20 s at 6.9 GB and
    growing, so memory is the limit and chunked evaluation is the lever.

## Later

- Hierarchical circuits (named blocks, congruence) and compact encodings
  decoded by the kernel, before any circuit above a few thousand gates.
- The wire-index decision (`Fin n` versus `ℕ` with well-formedness) before
  Rung 6 template work; then `cnotLadder n`, Toffoli as a macro, adders.
- Routing as `rename` by a permutation; ancilla subspaces as a side
  condition on congruence (Rung 5, only as Rung 6 needs it).
- `≡ₛ → ≡ₚ` for Clifford circuits (units and the prime over 2 in `ℤ[ω]`).
- `Zeta8.toComplex`, unitarity of every gate, the QECLean bridge.
- Dyadic normalisation tuning once the ring's measurements are in.
- Rung 8: the phase-polynomial form with phases in `ZMod (2 ^ m)` (the
  degree bound becomes `m`, so the planes grow with it).
- Kernel engineering: recursion depth on long lists, chunked replay.

## Done

- (this commit) Chunked evaluation (`CircuitEq/Chunk.lean`): `AllBelow`
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
