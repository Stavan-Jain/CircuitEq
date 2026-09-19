# CircuitEq — unitary equivalence of quantum circuits, in Lean 4

Two quantum circuits without measurements are unitaries. Are they the same
unitary? Existing checkers answer this for one fixed circuit size with one
built-in technique: decision diagrams, ZX-calculus rewriting, or path-sum
reduction. CircuitEq takes the other route. Circuits are Lean terms, the
question is a Lean proposition `c₁ ≡ᵤ c₂`, and a proof may use any
mathematics at all — kernel evaluation for a small concrete instance,
structural lemmas and induction for a family parametric in the qubit count,
or whatever a proof-search agent finds. The Lean kernel checks the result,
and every theorem in this repository depends on exactly mathlib's three
standard axioms.

The intended prover is an AI agent working with the toolkit here. The point
of the design is to make that agent's job mechanical where it can be
(`decide` is the oracle for leaves) and expressive where it must be
(structural lemmas that hold for every `n` are the connectives).

**Status: prototype.** Clifford+T only, one and two-qubit gates, some
twenty worked identities, four original-versus-PyZX benchmark pairs, and
certified checkers for the Clifford and the CNOT-plus-diagonal fragments.
See "Roadmap" for what is missing and `QUEUE.md` for what is next.

## What you can state and prove today

```lean
import CircuitEq
open Quantum.Circuit Instr

-- concrete: the kernel checks the 2^n computational-basis vectors
theorem hh_cnot_hh : ([H 0, H 1, CX 0 1, H 0, H 1] : Circuit 2) ≡ᵤ [CX 1 0] := by
  decide +kernel

-- concrete refutation, and the up-to-global-phase repair
theorem not_Z_X_comm : ¬ (([Z 0, X 0] : Circuit 1) ≡ᵤ [X 0, Z 0]) := by decide +kernel
theorem Z_X_phase_X_Z : ([Z 0, X 0] : Circuit 1) ≡ₚ [X 0, Z 0] := by decide +kernel

-- structural: for every qubit count n and every pair of distinct qubits
theorem H_T_H_eq_T {n} {i j : Fin n} (h : i ≠ j) : [H i, T j, H i] ≡ᵤ ([T j] : Circuit n) :=
  calc ([H i, T j, H i] : Circuit n) = [H i, T j] ++ [H i] := rfl
    _ ≡ᵤ [T j, H i] ++ [H i] := (one_one_comm h _ _).append (Equivalent.refl _)
    _ = [T j] ++ [H i, H i] := rfl
    _ ≡ᵤ [T j] ++ [] := (Equivalent.refl _).append (cancel_of_mul_eq_one Gate1.H_mul_H i)
    _ = [T j] := rfl

-- a layer of Hadamards on every qubit is self-inverse, for every n
theorem hLayer_cancel (n : ℕ) : hLayer n ++ hLayer n ≡ᵤ [] := hLayer_hLayer n

-- placed: a two-qubit identity the kernel decided, on any two wires of any register
theorem hh_cnot_hh' {n} {i j : Fin n} (h : i ≠ j) :
    [H i, H j, CX i j, H i, H j] ≡ᵤ ([CX j i] : Circuit n) := by
  simpa [wires₂] using hh_cnot_hh.rename (wires₂ h)

-- benchmark: PyZX's 13-gate Steane |+_L⟩ encoder equals the 19-gate original
theorem original_equiv_optimized : original ≡ᵤ optimized :=
  calc original
      = layer .H [0, 1, 3] ++ cnotNetwork edges ++ hLayer 7 := rfl
    _ ≡ᵤ _ := layer_cnotNetwork_hLayer [0, 1, 3] (by decide) edges (by decide)
    _ ≡ᵤ optimized := by circuit_simp

-- the window pattern: an optimiser's local rewrites, each decided on its own wires;
-- the tactic emits a certificate and the kernel replays it once
theorem two_windows :
    ([T 0, CX 1 2, T 0, H 5, X 3, H 5] : Circuit 6) ≡ᵤ [CX 1 2, S 0, X 3] := by
  circuit_windows [([T 0, T 0], [S 0]), ([H 5, H 5], [])]

-- fragment checkers: symbolic, linear in the gate count, never 2^n
theorem gadgets_merge :
    ([CX 0 1, T 1, CX 0 1, CX 0 1, T 1, CX 0 1] : Circuit 2) ≡ᵤ [CX 0 1, S 1, CX 0 1] :=
  (phasePolyChecker 2).sound _ _ (by decide +kernel)
theorem rm15 : original ≡ₛ optimized :=   -- 15 qubits, re-synthesised CNOT network, ~0.3 s
  (tableauChecker 15).sound _ _ (by decide +kernel)
```

Circuits are lists in time order, so `[g₁, g₂]` is the operator `U₂ · U₁`.
The qubit count is not inferable from `[H 0, T 0]` alone; ascribe one side
with `: Circuit n`. Use `decide +kernel`, not bare `decide` (see "Design").

`CircuitEq/Examples.lean` has the full set: decided identities (`T² = S`,
`HXH = Z`, `S X S† = Y`, `T⁸ = I`, both SWAP decompositions, CZ symmetry, a
three-qubit CNOT ladder), refutations (`HT ≠ TH`, `T` on a CNOT target does
not commute), and structural results for every `n` (`H²` cancels on any qubit,
`T` commutes through a CNOT on its control, Hadamard layers cancel).

[`benchmarks/rep3_phaseflip/`](benchmarks/rep3_phaseflip/README.md) adds an
original-versus-PyZX pair from QECUnitaryCircuits: the three-qubit
phase-flip repetition encoder, whose five gates PyZX only reorders. The pair
closes by `circuit_simp` in one line; `reorder` is the same fact for any
three distinct wires of any register.

[`benchmarks/steane_plus/`](benchmarks/steane_plus/README.md) proves a larger
pair: PyZX reduces the seven-qubit Steane logical plus-state encoder from
19 gates to 13, reversing all nine CNOTs. The proof is the five-line `calc`
above: one application of the parametric theorem that moves a Hadamard layer
through a CNOT network, then `circuit_simp` for the commuting remainder. No
step enumerates the seven-qubit basis.

[`benchmarks/tof_3/`](benchmarks/tof_3/README.md) is the first T-heavy pair:
the standard `tof_3` circuit (three Toffolis, T-count 21) against PyZX's
phase-teleportation output (T-count 19, gate skeleton preserved). One
`circuit_windows` call with four windows on at most three wires proves
exact equivalence; every other change is a phase gate moving through a CNOT
control. Full re-synthesis (T-count 15) is a structurally unrelated circuit
and out of the window pattern's reach.

[`benchmarks/rm15_zero/`](benchmarks/rm15_zero/README.md) is the first pair
decided by the Clifford tableau: the 15-qubit `[[15,1,3]]` Reed–Muller
logical-zero encoder against PyZX's re-synthesised CNOT network (32 to 28
gates, with CNOTs the original never has, so no alignment exists). The
proof is one line, `(tableauChecker 15).sound _ _ (by decide +kernel)`,
about 0.3 s of kernel time, and states `≡ₛ`, equality up to a unit scalar,
which is all a tableau can see.

[`benchmarks/barenco_tof_3/`](benchmarks/barenco_tof_3/README.md) is the
first pair whose alignment a script found rather than a person: Barenco's
three-controlled Toffoli, T-count 28 to 24 under phase teleportation, six
one-wire windows emitted by the survey's diff-based search and checked by
`circuit_windows` with no refinement.

[`benchmarks/scale/`](benchmarks/scale/README.md) pushes the checkers up
ladders of random and structured circuits. The phase-polynomial checker
certifies PyZX's phase folding of 200-, 400- and 800-gate random CNOT+T
circuits on 20, 40 and 80 qubits in 0.2, 0.6 and 1.9 s of kernel time, and
of a 10200-gate network of CCZ gadgets on 300 qubits in 10 s, refuting a
gate-deleted mutant of each; the ladder's first run found the earlier
parity-basis form incomplete, which is why the form is now the multilinear
polynomial. The tableau, proved one range of generators per declaration
(`CircuitEq/Chunk.lean`), certifies an 80-qubit random Clifford pair
re-synthesised into 8261 gates in 7 minutes, a 161-qubit round of
surface-code syndrome extraction in 39 s and two rounds on 241 qubits in
under three minutes; in one declaration it ran out of
memory at 40 qubits. The same chunking decides the seven-qubit Steane pair
on its full basis in 78 s under 2 GB, where the single `decide` was killed
at 7 GB.

[`benchmarks/survey/`](benchmarks/survey/README.md) is the evidence run for
the roadmap's working hypothesis: eleven T-heavy circuits (Toffoli chains,
Barenco's Toffoli, `mod5_4`, Cuccaro adders, seeded random circuits) against
both PyZX pipelines, aligned by script. Phase-teleportation output aligns
by windows on the structured circuits (seven pairs kernel-checked in 2 to
10 s each on the dyadic evaluator, one memory-bound), re-synthesised output
never does except as a whole-register decide, three random pairs are equal
only up to a global phase, and every wide window is CNOT-plus-diagonal
segments around one Hadamard, which is where the phase-polynomial checker
applies next.

## Design

- **Coefficients are the computable field ℚ(ζ₈), not ℂ.** Mathlib's `ℂ` is
  noncomputable, so nothing over it can be decided by evaluation. Every
  Clifford+T matrix entry lies in `ℤ[1/√2, i] ⊂ ℚ(ζ₈)`, and `ℚ(ζ₈)` is four
  rational coordinates in the power basis of `ω = e^{iπ/4}` with `ω⁴ = -1`.
  That is `Quantum.Zeta8`, a `CommRing` and `StarRing` whose axioms are
  coordinate-wise identities.
- **Gates act sparsely on state vectors.** A gate on qubit `i` is not
  `I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I`; it is the state-vector update
  `applyOne G i ψ x = G[b,b]·ψ x + G[b,¬b]·ψ (flipBit i x)` with `b = bit i x`,
  and `applyCNOT c t ψ x = if bit c x then ψ (flipBit t x) else ψ x`. Each
  output amplitude reads two inputs, so the kernel pays `O(1)` per entry, and
  the structural lemmas — disjoint gates commute, same-qubit gates fuse — are
  pointwise `ring` identities after four bit lemmas.
- **Equivalence reduces to the basis.** `c₁ ≡ᵤ c₂` is `∀ ψ, denote c₁ ψ =
  denote c₂ ψ`. Every instruction is linear, so `LinearMap.pi_ext` reduces
  this to the `2 ^ n` basis vectors, which gives a `Decidable` instance.
  `≡ₚ` additionally ranges over the eight powers of `ω`. The instance
  evaluates with a closure evaluator over `Dyadic8` (`Dyadic.lean`), the
  gcd-free ring `ℤ[ω, 1/√2]`, proved equal to `denote`, so the kernel never
  sees a rational and a decide is linear in depth: a three-qubit six-gate
  window is 0.09 s where the rational list evaluator took 3 s.
- **Kernel-only.** `decide +kernel` is required because `Rat.add` and
  `Rat.mul` are `@[irreducible]`, which stalls elaborator-level `decide`; the
  kernel ignores reducibility and evaluates `Nat.gcd` with GMP. No
  `native_decide` anywhere, enforced by `scripts/AxiomCheck.lean` in CI,
  and CI replays the built `.olean` files through the kernel, so a leaf
  that skipped the kernel cannot hide (see "Trust").
- **The structural toolkit is the agent's vocabulary.** `fuse`, `fuse₃`,
  `cancel_of_mul_eq_one`, `one_one_comm`, `cnot_diag_control_comm`,
  `denote_applyOne_comm_of_not_touches` (move a gate past any circuit that
  ignores its qubit), `layer_layer_cancel`. Each is stated on `≡ᵤ` for
  arbitrary `n` with `2 × 2` matrix leaves decided by the kernel.
- **Rewriting happens on instruction lists, not state vectors.**
  `Equivalent.in_context` replaces an equivalent window inside any prefix and
  suffix; `Instr.CanCommute` and `Instr.CanCancel` are decidable syntactic
  checks whose `sound` lemmas produce the semantic swap or cancellation
  (`CanCommute` knows disjoint wires, diagonal gates on one wire, a
  diagonal gate on a CNOT control, `X` on a CNOT target, and CNOTs whose
  controls avoid each other's targets);
  `gate_block_comm`, `blocks_comm`, `perm_equivalent`, `pull_cons` and
  `cancel_window` move gates and blocks. A benchmark proof never mentions
  `denote` or an amplitude vector.
- **Layers and networks are first-class.** `layer_cnotNetwork_hLayer` moves
  a Hadamard layer through a whole CNOT network in one step, reversing every
  CNOT and cancelling against the seed layer, for every `n`; `hOn_symmDiff`
  is the algebra of partial Hadamard layers (`hOn S ++ hOn T ≡ᵤ hOn (S ∆ T)`);
  `cnotNetwork_perm` reorders a network with disjoint controls and targets.
- **Certificates, not proof terms.** `Certificate.lean` is a data type of
  rewrite steps (`swap`, `moveLeft`/`moveRight` across a block with a
  disjoint bitmask support, `cancel`/`insert`, `window` on named wires
  justified by a checker from a table) with a kernel-friendly interpreter
  `replay` and one theorem `replay_sound`. A proof is
  `replay_sound Cs steps (by decide +kernel)`: the kernel evaluates
  `replay` once, cost linear in the trace. `scripts/certificate.py` mirrors
  the language in Python so external tools can emit traces.
- **The tactics emit certificates.** `circuit_simp` cancels checked inverse
  pairs and aligns two concrete lists; `circuit_windows` takes an alignment
  as input, a list of windows `(aᵢ, bᵢ)` on the full register in the order
  they occur, and checks every other move as a commutation. Both search in
  meta, emit a `List Step`, and close the goal with a single `replay_sound`.
  Neither searches for alignments: a move the checks do not license, or a
  false window, is an error naming the gate or the window.
- **Fragment checkers decide windows symbolically.** `PhasePoly.lean` is a
  certified canonical form for CNOT-plus-diagonal circuits (an
  `𝔽₂`-linear part as packed row bitmasks, the phase function as its
  multilinear polynomial over `ℤ/8`, degree at most three, as `Nat` bit
  planes): linear in gates, independent of `2 ^ n`, complete on its
  fragment (equal unitaries give equal forms, so `phasePolyRefutes`
  proves inequivalence), and the deterministic counterpart of what
  T-count optimisers such as TZAP compute. `Tableau.lean` conjugates the
  `2n` Pauli generators through a Clifford circuit with `O(n)` bit
  operations per gate and certifies `≡ₛ`, equality up to a unit scalar,
  by the commutant argument on state vectors. Both export the `Checker`
  contract of `Checker.lean`, and the default certificate table tries the
  phase polynomial before the basis evaluator.
- **The locality theorem.** `rename f c` places an `m`-qubit circuit on the
  wires `f : Fin m ↪ Fin n`; `rename_equivalent_iff` says
  `rename f a ≡ᵤ rename f b ↔ a ≡ᵤ b`. So a `decide +kernel` on `m` qubits,
  at cost `2 ^ m`, yields the identity on any `m` distinct wires of any
  register, and a window that touches `m` wires costs `2 ^ m`, never `2 ^ n`.

## Layout

```
CircuitEq.lean              umbrella
CircuitEq/
├── Zeta8.lean              ℚ(ζ₈): the computable coefficient field
├── Bits.lean               bit / flipBit on Fin (2 ^ n), commutation lemmas
├── Gates.lean              Gate1 alphabet, 2×2 matrices, applyOne / applyCNOT
├── Dyadic.lean             ℤ[ω, 1/√2]: the gcd-free ring the kernel computes in
├── Chunk.lean              chunked kernel evaluation: one declaration per index range
├── Semantics.lean          Instr, Circuit, denote, ≡ᵤ, ≡ₚ, ≡ₛ, decidability
├── Checker.lean            the checker contract: check + sound, normal forms
├── Structural.lean         the parametric toolkit: fusion, commutation, layers
├── Support.lean            wire sets as Nat bitmasks
├── PhasePoly.lean          phase-polynomial normal form, CNOT + diagonal
├── Tableau.lean            Clifford tableau checker, soundness to ≡ₛ
├── Rewriting.lean          rewriting in context, checked swaps and cancellations
├── Layers.lean             Hadamard-layer algebra, CNOT-network conjugation
├── Certificate.lean        Step, replay, replay_sound, the checker table
├── Tactic.lean             circuit_simp, circuit_windows (emit certificates)
├── Embedding.lean          the locality theorem: circuits on selected wires
├── Examples.lean           worked identities: decided, refuted, structural, placed
└── Benchmarks/             original-versus-PyZX proofs
benchmarks/                 QASM fixtures and provenance for each benchmark
scripts/AxiomCheck.lean     CI: standard three axioms only
scripts/check_debug_options.py     CI: text guard against debug.* options
scripts/SkipKernelTCFixture.lean   the repro the kernel replay must reject
scripts/check_replay_fixture.sh    CI: asserts that it does
scripts/check_pyzx_benchmarks.py   reproduce the PyZX fixtures (pyzx==0.9.0)
scripts/certificate.py      Python mirror of the certificate language
scripts/scale_test.py       the scale ladder; scripts/chunked_decide.py, chunks.py
QUEUE.md                    the ordered list of next work
```

## Building

```bash
lake exe cache get   # mathlib oleans (one-time, several GB)
lake build
lake env lean scripts/AxiomCheck.lean
LEAN_NUM_THREADS=1 lake env leanchecker CircuitEq   # kernel replay, see "Trust"
```

If [QECLean](https://github.com/Stavan-Jain/QECLean) is checked out as a
sibling directory with mathlib already built, skip the download: the two
projects pin the same mathlib commit, so

```bash
rm -rf .lake/packages && ln -s ../../QECLean/.lake/packages .lake/packages
```

shares its immutable dependency artifacts (only `.lake/packages`; this
project's own `.lake/build` stays separate). Keep `lake-manifest.json` in step
with QECLean's when bumping mathlib, or drop the symlink and use the cache.

## Roadmap

[`ROADMAP.md`](ROADMAP.md) is the full ladder: twelve rungs from the prototype
to modular arithmetic for Shor for all `n`, each with an acceptance test.
Scale on real compiled circuits that today's checkers cannot handle is the
goal; parametric theorems about circuit templates are the method; kernel-level
trust is the byproduct. Basic equivalence, exact or up to a global phase,
carries the whole S-critical path; refined relations on ancilla subspaces are
introduced only when constructions that use ancillas need them. Near term: a
materialised evaluator so concrete checks scale with depth; a
conformance-checked OpenQASM generator and the bridge to ℂ; a locality theorem
and compositional proofs of fixed-size optimiser-output pairs; then the first
parametric templates, ripple-carry adders and multi-controlled gates for every
`n`.

## Trust

Every declaration must depend on exactly `[propext, Classical.choice,
Quot.sound]`. `scripts/AxiomCheck.lean` walks the whole library and fails CI
otherwise. `native_decide` is banned; `sorry` is for WIP branches only. Check a
single result with `#print axioms Quantum.Circuit.Examples.hh_cnot_hh`.

The axiom check is half of the policy, because it cannot see a declaration
that never reached the kernel. `set_option debug.skipKernelTC true` makes
Lean add a declaration unchecked, and `decide +kernel`, the leaf of every
proof here, leaves its whole check to the kernel: under the option
`2 + 2 = 5` elaborates without an error and `#print axioms` reports no
axioms. So CI also replays every declaration of the built `.olean` files
through the kernel, in a process where no option or meta code of the library
runs:

```bash
LEAN_NUM_THREADS=1 lake env leanchecker CircuitEq   # about 30 s, 0.4 GB
```

`leanchecker` is the former lean4checker; it ships inside the toolchain
since Lean v4.28, so it always matches `lean-toolchain`. One thread is
deliberate: every parallel replay loads its own copy of the mathlib imports,
about 2 GB per extra thread, and the default thread count does not fit in
16 GB. `scripts/SkipKernelTCFixture.lean` keeps the `2 + 2 = 5` repro outside
every `lean_lib`, and `scripts/check_replay_fixture.sh` asserts on every CI
run that it still compiles clean and that the replay rejects it, so a
toolchain bump cannot quietly turn the replay into a no-op.
`scripts/check_debug_options.py` fails CI early when a `debug.*` option is
set in the Lean sources or in `lakefile.toml`. That guard is a text search,
an early warning and not sound: an option can be set from meta code under a
name no search recognises. The replay is the defence.

What the replay does not do: it re-checks this library's modules against
their imports as delivered, so mathlib and core are trusted as the cache
provides them, and it is the Lean kernel again, not an independent checker.

## Related

- [QECLean](https://github.com/Stavan-Jain/QECLean): stabilizer-formalism
  library this grew out of; shares the `Quantum` namespace and mathlib pin.
- [QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits):
  purely unitary Clifford+T QEC circuits in OpenQASM, a future benchmark input.
- [qec-lab](https://github.com/Stavan-Jain/qec-lab): research workbench and
  the `docs/mathlib-version-quirks.md` where the quirks above are recorded.

## License

Apache 2.0, see `LICENSE`.
