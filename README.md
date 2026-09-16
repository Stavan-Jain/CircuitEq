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
twenty worked identities, three original-versus-PyZX benchmark pairs. See
"Roadmap" for what is missing.

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

-- the window pattern: an optimiser's local rewrites, each decided on its own wires
theorem two_windows :
    ([T 0, CX 1 2, T 0, H 5, X 3, H 5] : Circuit 6) ≡ᵤ [CX 1 2, S 0, X 3] := by
  circuit_windows [([T 0, T 0], [S 0]), ([H 5, H 5], [])]
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
  evaluates with `evalList`, a materialised list-backed evaluator proved
  equal to `denote`, so a decide costs linear in circuit depth, not
  `2 ^ depth`.
- **Kernel-only.** `decide +kernel` is required because `Rat.add` and
  `Rat.mul` are `@[irreducible]`, which stalls elaborator-level `decide`; the
  kernel ignores reducibility and evaluates `Nat.gcd` with GMP. No
  `native_decide` anywhere, enforced by `scripts/AxiomCheck.lean` in CI.
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
- **`circuit_simp` does the routine.** Given `c₁ ≡ᵤ c₂` on concrete lists, it
  cancels checked inverse pairs through the gates they commute with, then
  aligns the two lists by pulling each gate of `c₂` through a checked prefix
  of `c₁`. It assembles ordinary proof terms from `cancel_window` and
  `pull_cons`; block identities remain explicit steps in the calling proof.
- **`circuit_windows` is the window pattern.** The alignment is input: a
  list of windows `(aᵢ, bᵢ)`, each a pair of gate lists on the full register
  touching a few wires, in the order they occur. The tactic decides each
  window on its own wires by `decide +kernel` (cost `2 ^ k`, never `2 ^ n`),
  places it back with the locality theorem (`Equivalent.of_rename`), and
  checks every other move as a commutation. It never searches: a move the
  checks do not license, or a false window, is an error naming the gate or
  the window.
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
├── Semantics.lean          Instr, Circuit, denote, ≡ᵤ, ≡ₚ, decidability
├── Structural.lean         the parametric toolkit: fusion, commutation, layers
├── Rewriting.lean          rewriting in context, checked swaps and cancellations
├── Layers.lean             Hadamard-layer algebra, CNOT-network conjugation
├── Tactic.lean             circuit_simp, circuit_windows
├── Embedding.lean          the locality theorem: circuits on selected wires
├── Examples.lean           worked identities: decided, refuted, structural, placed
└── Benchmarks/             original-versus-PyZX proofs
benchmarks/                 QASM fixtures and provenance for each benchmark
scripts/AxiomCheck.lean     CI: standard three axioms only
scripts/check_pyzx_benchmarks.py   reproduce the PyZX fixtures (pyzx==0.9.0)
```

## Building

```bash
lake exe cache get   # mathlib oleans (one-time, several GB)
lake build
lake env lean scripts/AxiomCheck.lean
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

## Related

- [QECLean](https://github.com/Stavan-Jain/QECLean): stabilizer-formalism
  library this grew out of; shares the `Quantum` namespace and mathlib pin.
- [QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits):
  purely unitary Clifford+T QEC circuits in OpenQASM, a future benchmark input.
- [qec-lab](https://github.com/Stavan-Jain/qec-lab): research workbench and
  the `docs/mathlib-version-quirks.md` where the quirks above are recorded.

## License

Apache 2.0, see `LICENSE`.
