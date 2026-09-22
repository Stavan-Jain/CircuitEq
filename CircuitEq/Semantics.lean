/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Gates

/-!
# Circuits, their denotation, and the equivalence relations

This file, with the gate semantics it builds on (`Gate1.mat`, `applyOne`,
`applyCNOT` in `CircuitEq.Gates`, `bit` and `flipBit` in `CircuitEq.Bits`,
the field in `CircuitEq.Zeta8`), is the trusted core: what a circuit is, what
it means, and what it means for two circuits to be equivalent. Everything
else in the library is proved against these definitions, and nothing here is proved about them
beyond the facts about `denote` that every other file uses.

A `Circuit n` is a list of instructions (`Instr n`: a single-qubit
Clifford+T gate on a named qubit, or a CNOT) in time order. Its denotation
`denote c : Vec n → Vec n` applies the instructions left to right, so as an
operator the circuit `[g₁, g₂, g₃]` is `U₃ · U₂ · U₁`.

## The relations

- `c₁ ≡ᵤ c₂` (`Equivalent`): the two denotations agree on every amplitude
  vector.
- `c₁ ≡ₚ[k] c₂` (`EquivalentWithPhase`): as operators, `c₁` is `ω ^ k`
  times `c₂`, with `k : Fin 8`.
- `c₁ ≡ₚ c₂` (`EquivalentUpToPhase`): `∃ k, c₁ ≡ₚ[k] c₂`. For Clifford+T a
  global phase is one of the eight powers of `ω`, and optimisers preserve a
  circuit only up to one.
- `c₁ ≡ₛ c₂` (`EquivalentUpToScalar`): equal up to a unit of the
  coefficient ring; what a Clifford tableau certifies.

Their algebra (`refl`, `symm`, `trans`, `append`, and for the first three
`cons` and `calc`) is in `CircuitEq.Relations`. Their decision procedures, the reduction to the
computational basis and the evaluators the kernel runs, are in
`CircuitEq.Decide`.

## Why state vectors, not matrices

`denote` is defined on vectors, not as a `2 ^ n × 2 ^ n` matrix, because
the kernel then evaluates a gate in `O(1)` per amplitude with no `Finset.sum`
to unfold, and because the structural lemmas (gates on disjoint qubits
commute, same-qubit gates fuse) are pointwise identities.
-/

namespace Quantum.Circuit

variable {n : ℕ}

/-- One instruction: a single-qubit Clifford+T gate on qubit `i`, or a CNOT
with control `c` and target `t`. -/
inductive Instr (n : ℕ) where
  | one (g : Gate1) (i : Fin n)
  | cnot (c t : Fin n)
  deriving DecidableEq, Repr

end Quantum.Circuit

namespace Quantum

/-- A circuit on `n` qubits: instructions in time order, earliest first. -/
abbrev Circuit (n : ℕ) := List (Circuit.Instr n)

namespace Circuit

variable {n : ℕ}

namespace Instr

/-! Readable constructors, so a circuit reads `[H 0, CX 0 1, T 1]`. -/

/-- Hadamard on qubit `i`. -/
abbrev H (i : Fin n) : Instr n := one .H i
/-- Pauli `X` on qubit `i`. -/
abbrev X (i : Fin n) : Instr n := one .X i
/-- Pauli `Y` on qubit `i`. -/
abbrev Y (i : Fin n) : Instr n := one .Y i
/-- Pauli `Z` on qubit `i`. -/
abbrev Z (i : Fin n) : Instr n := one .Z i
/-- Phase gate `S = diag(1, i)` on qubit `i`. -/
abbrev S (i : Fin n) : Instr n := one .S i
/-- `S†` on qubit `i`. -/
abbrev Sdg (i : Fin n) : Instr n := one .Sdg i
/-- `T = diag(1, ω)` on qubit `i`. -/
abbrev T (i : Fin n) : Instr n := one .T i
/-- `T†` on qubit `i`. -/
abbrev Tdg (i : Fin n) : Instr n := one .Tdg i
/-- CNOT with control `c` and target `t`. -/
abbrev CX (c t : Fin n) : Instr n := cnot c t

/-- The action of one instruction on amplitude vectors. -/
def apply : Instr n → Vec n → Vec n
  | one g i => applyOne g.mat i
  | cnot c t => applyCNOT c t

@[simp] lemma apply_one (g : Gate1) (i : Fin n) (ψ : Vec n) :
    (one g i).apply ψ = applyOne g.mat i ψ := rfl

@[simp] lemma apply_cnot (c t : Fin n) (ψ : Vec n) :
    (cnot c t).apply ψ = applyCNOT c t ψ := rfl

lemma apply_add (g : Instr n) (ψ φ : Vec n) : g.apply (ψ + φ) = g.apply ψ + g.apply φ := by
  cases g <;> simp [applyOne_add, applyCNOT_add]

lemma apply_smul (g : Instr n) (a : Zeta8) (ψ : Vec n) : g.apply (a • ψ) = a • g.apply ψ := by
  cases g <;> simp [applyOne_smul, applyCNOT_smul]

end Instr

/-! ### Denotation -/

/-- Denotation: apply the instructions in list order. -/
def denote : Circuit n → Vec n → Vec n
  | [], ψ => ψ
  | g :: c, ψ => denote c (g.apply ψ)

@[simp] lemma denote_nil (ψ : Vec n) : denote [] ψ = ψ := rfl

@[simp] lemma denote_cons (g : Instr n) (c : Circuit n) (ψ : Vec n) :
    denote (g :: c) ψ = denote c (g.apply ψ) := rfl

@[simp] lemma denote_append (c₁ c₂ : Circuit n) (ψ : Vec n) :
    denote (c₁ ++ c₂) ψ = denote c₂ (denote c₁ ψ) := by
  induction c₁ generalizing ψ with
  | nil => rfl
  | cons g c ih => simp [ih]

lemma denote_add (c : Circuit n) (ψ φ : Vec n) : denote c (ψ + φ) = denote c ψ + denote c φ := by
  induction c generalizing ψ φ with
  | nil => rfl
  | cons g c ih => simp [Instr.apply_add, ih]

lemma denote_smul (c : Circuit n) (a : Zeta8) (ψ : Vec n) : denote c (a • ψ) = a • denote c ψ := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih => simp [Instr.apply_smul, ih]

/-! ### The relations -/

/-- Unitary equivalence: the circuits act identically on every amplitude
vector, i.e. they denote the same operator. -/
def Equivalent (c₁ c₂ : Circuit n) : Prop := ∀ ψ : Vec n, denote c₁ ψ = denote c₂ ψ

@[inherit_doc] scoped infix:50 " ≡ᵤ " => Equivalent

/-- Equivalence with a *named* global phase: as operators, `c₁` is `ω ^ k`
times `c₂`. This is the form in which phases compose: the exponents add in
`Fin 8`, that is, modulo eight, which is how `ω` behaves
(`Zeta8.ω_pow_val_add`). -/
def EquivalentWithPhase (k : Fin 8) (c₁ c₂ : Circuit n) : Prop :=
  ∀ ψ : Vec n, denote c₁ ψ = Zeta8.ω ^ (k : ℕ) • denote c₂ ψ

@[inherit_doc] scoped notation:50 c₁:51 " ≡ₚ[" k "] " c₂:51 => EquivalentWithPhase k c₁ c₂

/-- Equivalence up to a global phase: some phase can be named. For
Clifford+T a global phase is a power of `ω = ζ₈`, so it ranges over
`Fin 8`. -/
def EquivalentUpToPhase (c₁ c₂ : Circuit n) : Prop :=
  ∃ k : Fin 8, EquivalentWithPhase k c₁ c₂

@[inherit_doc] scoped infix:50 " ≡ₚ " => EquivalentUpToPhase

/-- Equivalence up to a global scalar that is a unit of the coefficient
ring. For unitaries the scalar has modulus one, and for Clifford+T it is a
power of `ω`, but that is a theorem about the ring rather than part of the
definition; this is the relation a Clifford tableau certifies. -/
def EquivalentUpToScalar (c₁ c₂ : Circuit n) : Prop :=
  ∃ a : Zeta8, IsUnit a ∧ ∀ ψ : Vec n, denote c₁ ψ = a • denote c₂ ψ

@[inherit_doc] scoped infix:50 " ≡ₛ " => EquivalentUpToScalar

end Circuit

end Quantum
