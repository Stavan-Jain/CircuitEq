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

- **T-count survey.** `scripts/tcount_survey.py`, `benchmarks/survey/`:
  Toffoli chains, adders and seeded random circuits against both PyZX
  pipelines, diff-based alignments checked by `circuit_windows`, and a
  written account of what does not align. M. Early records: teleport
  alignments tend to a single whole-register window (a brute-force decide,
  not a window proof), and `full_reduce` pairs have no alignment.

## Next

1. **Integrate the survey.** Merge its branch, fold its table and failure
   modes into ROADMAP Rung 3 and this file, and turn its findings into
   items below. S. Depends on the survey branch. (The other four branches
   are merged; `phasePolyChecker` is registered at index 0 of
   `defaultCheckers` with `evalChecker` as fallback. `tableauChecker`
   cannot join that table: it certifies `≡ₛ`; see item 11.)

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
   which pairs still need the residual pattern. S. Depends on items 1
   and 3.

6. **Phase-polynomial follow-ups.** Completeness (equal unitaries in the
   fragment give equal forms, so `false` is a refutation); the affine `X`
   extension (a constant bit per row); `ofNF` resynthesis with
   `nf (ofNF x) = some x`, which turns any untrusted synthesis heuristic
   into a certified T-count optimiser for the fragment. M. Depends on
   nothing; resynthesis is the first optimiser deliverable.

7. **The 19-origin Clifford run.** Every QECUnitaryCircuits origin against
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
   the two tableaux differ. Needed for mutants and for the survey's
   negative results. S. Depends on item 1.

10. **Rung 2 conformance.** A Qiskit statevector check of
    `lean_instructions` on the benchmark files and a few hundred random
    circuits (the `rz` global-phase trap), run in CI. S. Depends on
    nothing.

11. **The scalar replay.** A `ScalarCheckerTable`, a window step whose
    soundness uses `EquivalentUpToScalar.append` and a rename lemma for
    `≡ₛ`, and `replayₛ_sound : … → c ≡ₛ c'`, so that `tableauChecker` can
    justify windows and, later, residuals. Until then the tableau is used
    whole-circuit only. S to M. Depends on nothing.

12. **A block-theorem step.** A step kind that applies a registered lemma
    such as `layer_cnotNetwork_hLayer` at a position, so the Steane proof
    and the Python mirror no longer need a `calc` around the certificate;
    this is the first form of the template step of item 4. S. Depends on
    nothing.

13. **Measure the seven-qubit decide on an idle machine.** `original ≡ᵤ
    optimized` from `SteanePlus.lean` by `decide +kernel` under the dyadic
    evaluator, with the machine otherwise idle and a memory cap; the
    estimate is tens of seconds and a few GB. If memory is the limit, the
    kernel's `whnf` cache is the reason and chunked evaluation is the
    lever. S. Depends on nothing but a quiet machine.

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
- Rung 8: the phase-polynomial form with phases in `ZMod (2 ^ m)`.
- Kernel engineering: recursion depth on long lists, chunked replay.

## Done

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
