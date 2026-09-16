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

**Status: prototype.** Clifford+T only, one and two-qubit gates, twenty
worked identities. See "Roadmap" for what is missing.

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
```

Circuits are lists in time order, so `[g₁, g₂]` is the operator `U₂ · U₁`.
The qubit count is not inferable from `[H 0, T 0]` alone; ascribe one side
with `: Circuit n`. Use `decide +kernel`, not bare `decide` (see "Design").

`CircuitEq/Examples.lean` has the full set: decided identities (`T² = S`,
`HXH = Z`, `S X S† = Y`, `T⁸ = I`, both SWAP decompositions, CZ symmetry, a
three-qubit CNOT ladder), refutations (`HT ≠ TH`, `T` on a CNOT target does
not commute), and structural results for every `n` (`H²` cancels on any qubit,
`T` commutes through a CNOT on its control, Hadamard layers cancel).

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
  `≡ₚ` additionally ranges over the eight powers of `ω`.
- **Kernel-only.** `decide +kernel` is required because `Rat.add` and
  `Rat.mul` are `@[irreducible]`, which stalls elaborator-level `decide`; the
  kernel ignores reducibility and evaluates `Nat.gcd` with GMP. No
  `native_decide` anywhere, enforced by `scripts/AxiomCheck.lean` in CI.
- **The structural toolkit is the agent's vocabulary.** `fuse`, `fuse₃`,
  `cancel_of_mul_eq_one`, `one_one_comm`, `cnot_diag_control_comm`,
  `denote_applyOne_comm_of_not_touches` (move a gate past any circuit that
  ignores its qubit), `layer_layer_cancel`. Each is stated on `≡ᵤ` for
  arbitrary `n` with `2 × 2` matrix leaves decided by the kernel.

## Layout

```
CircuitEq.lean              umbrella
CircuitEq/
├── Zeta8.lean              ℚ(ζ₈): the computable coefficient field
├── Bits.lean               bit / flipBit on Fin (2 ^ n), commutation lemmas
├── Gates.lean              Gate1 alphabet, 2×2 matrices, applyOne / applyCNOT
├── Semantics.lean          Instr, Circuit, denote, ≡ᵤ, ≡ₚ, decidability
├── Structural.lean         the parametric toolkit
└── Examples.lean           worked identities: decided, refuted, structural
scripts/AxiomCheck.lean     CI: standard three axioms only
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

[`ROADMAP.md`](ROADMAP.md) is the full ladder: eleven rungs from the prototype
to modular arithmetic for Shor for all `n`, each with an acceptance test and a
statement of what it delivers beyond current checkers (parametric, scale, or
trust). Near term: a materialised evaluator so concrete checks scale with
depth; OpenQASM ingestion and a differential test of the semantics; the
equivalence notions compilers need (permutation, ancilla, subspace); then the
first useful parametric theorems, ripple-carry adders and multi-controlled
gates for every `n`.

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
