/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Gates
import Mathlib.LinearAlgebra.Pi

/-!
# Circuits, their denotation, and unitary equivalence

A `Circuit n` is a list of instructions (`Instr n`: a single-qubit
Clifford+T gate on a named qubit, or a CNOT) in time order. Its denotation
`denote c : Vec n → Vec n` applies the instructions left to right, so as an
operator the circuit `[g₁, g₂, g₃]` is `U₃ · U₂ · U₁`.

## Equivalence

`c₁ ≡ᵤ c₂` (`Equivalent`) says the two denotations agree on every amplitude
vector. Because each instruction is linear, agreement on the `2 ^ n`
computational-basis vectors suffices (`equivalent_iff_basis`), and that is a
finite check the kernel can run: `Decidable (c₁ ≡ᵤ c₂)` is provided, so
concrete equivalences and non-equivalences close by `decide +kernel`.

`c₁ ≡ₚ c₂` (`EquivalentUpToPhase`) allows a global phase, which for
Clifford+T is one of the eight powers of `ω`, so it is decidable the same way.

The instances evaluate through `evalList`, a materialised list-backed
evaluator proved equal to `denote` (`evalList_toList`), so the kernel's
cost is linear in depth; `denote` itself is nested closures.

## Why state vectors, not matrices

`denote` is defined on vectors, not as a `2 ^ n × 2 ^ n` matrix, because
the kernel then evaluates a gate in `O(1)` per amplitude with no `Finset.sum`
to unfold, and because the structural lemmas (gates on disjoint qubits
commute, same-qubit gates fuse) are pointwise identities. The linear-map view
`denoteₗ` is available for the basis-reduction argument.
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

/-- The denotation as a linear map on amplitude vectors. -/
def denoteₗ (c : Circuit n) : Vec n →ₗ[Zeta8] Vec n where
  toFun := denote c
  map_add' := denote_add c
  map_smul' := denote_smul c

@[simp] lemma denoteₗ_apply (c : Circuit n) (ψ : Vec n) : denoteₗ c ψ = denote c ψ := rfl

/-! ### Unitary equivalence -/

/-- Unitary equivalence: the circuits act identically on every amplitude
vector, i.e. they denote the same operator. -/
def Equivalent (c₁ c₂ : Circuit n) : Prop := ∀ ψ : Vec n, denote c₁ ψ = denote c₂ ψ

@[inherit_doc] scoped infix:50 " ≡ᵤ " => Equivalent

/-- Equivalence up to a global phase. For Clifford+T the phase is a power of
`ω = ζ₈`, so it ranges over `Fin 8`. -/
def EquivalentUpToPhase (c₁ c₂ : Circuit n) : Prop :=
  ∃ k : Fin 8, ∀ ψ : Vec n, denote c₁ ψ = Zeta8.ω ^ (k : ℕ) • denote c₂ ψ

@[inherit_doc] scoped infix:50 " ≡ₚ " => EquivalentUpToPhase

namespace Equivalent

@[refl] protected lemma refl (c : Circuit n) : c ≡ᵤ c := fun _ => rfl

@[symm] protected lemma symm {c₁ c₂ : Circuit n} (h : c₁ ≡ᵤ c₂) : c₂ ≡ᵤ c₁ :=
  fun ψ => (h ψ).symm

@[trans] protected lemma trans {c₁ c₂ c₃ : Circuit n} (h₁ : c₁ ≡ᵤ c₂) (h₂ : c₂ ≡ᵤ c₃) :
    c₁ ≡ᵤ c₃ :=
  fun ψ => (h₁ ψ).trans (h₂ ψ)

/-- Equivalence is a congruence for sequential composition. -/
protected lemma append {c₁ c₁' c₂ c₂' : Circuit n} (h₁ : c₁ ≡ᵤ c₁') (h₂ : c₂ ≡ᵤ c₂') :
    c₁ ++ c₂ ≡ᵤ c₁' ++ c₂' := by
  intro ψ
  simp [h₁ ψ, h₂ _]

/-- Prepending the same instruction preserves equivalence. -/
protected lemma cons (g : Instr n) {c c' : Circuit n} (h : c ≡ᵤ c') : g :: c ≡ᵤ g :: c' :=
  fun ψ => h (g.apply ψ)

/-- Exact equivalence is equivalence with trivial phase. -/
lemma toUpToPhase {c₁ c₂ : Circuit n} (h : c₁ ≡ᵤ c₂) : c₁ ≡ₚ c₂ :=
  ⟨0, fun ψ => by simp [h ψ]⟩

end Equivalent

/-- `calc` support: chaining `≡ᵤ` with `≡ᵤ` (chaining with `=` is built in). -/
instance : @Trans (Circuit n) (Circuit n) (Circuit n) Equivalent Equivalent Equivalent :=
  ⟨Equivalent.trans⟩

/-! ### Reduction to the computational basis -/

/-- The computational-basis vector `|y⟩`. -/
def basis (y : Fin (2 ^ n)) : Vec n := fun x => if x = y then 1 else 0

lemma basis_eq_single (y : Fin (2 ^ n)) : basis y = Pi.single y 1 := by
  funext x
  simp [basis, Pi.single_apply]

/-- Linear maps on `Vec n` that agree on the computational basis agree. -/
lemma LinearMap.ext_basis {f g : Vec n →ₗ[Zeta8] Vec n}
    (h : ∀ y, f (basis y) = g (basis y)) : f = g := by
  apply _root_.LinearMap.pi_ext
  intro y a
  have ha : (Pi.single y a : Vec n) = a • basis y := by
    rw [basis_eq_single, ← Pi.single_smul, smul_eq_mul, mul_one]
  rw [ha, map_smul, map_smul, h y]

/-- Two circuits are equivalent iff they agree on the `2 ^ n` basis vectors.
This is what makes `Equivalent` decidable for concrete circuits. -/
theorem equivalent_iff_basis (c₁ c₂ : Circuit n) :
    c₁ ≡ᵤ c₂ ↔ ∀ y, denote c₁ (basis y) = denote c₂ (basis y) := by
  refine ⟨fun h y => h _, fun h ψ => ?_⟩
  have : denoteₗ c₁ = denoteₗ c₂ := LinearMap.ext_basis h
  exact LinearMap.congr_fun this ψ

/-- Equivalence up to phase, reduced to the computational basis. -/
theorem equivalentUpToPhase_iff_basis (c₁ c₂ : Circuit n) :
    c₁ ≡ₚ c₂ ↔ ∃ k : Fin 8, ∀ y, denote c₁ (basis y) = Zeta8.ω ^ (k : ℕ) • denote c₂ (basis y) := by
  refine ⟨fun ⟨k, hk⟩ => ⟨k, fun y => hk _⟩, fun ⟨k, hk⟩ => ⟨k, fun ψ => ?_⟩⟩
  have : denoteₗ c₁ = Zeta8.ω ^ (k : ℕ) • denoteₗ c₂ := LinearMap.ext_basis fun y => by
    rw [_root_.LinearMap.smul_apply, denoteₗ_apply, denoteₗ_apply, hk y]
  simpa using LinearMap.congr_fun this ψ

/-! ### A materialised evaluator for the kernel

`denote` builds nested closures, so reading one amplitude of a depth-`d`
circuit re-reads the input up to `2 ^ d` times. For the decision procedure
the state is instead kept as a list of `2 ^ n` amplitudes and each
instruction reads the previous list once per output entry, `O(d · 4 ^ n)`
list steps in all. `evalList_toList` is the correspondence with `denote`,
and the `Decidable` instances go through it. -/

/-- A state as its list of amplitudes: entry `x` is `ψ x`. -/
def Vec.toList (ψ : Vec n) : List Zeta8 := List.ofFn ψ

/-- A list of amplitudes as a state (`0` past the end, which does not happen
for lists of length `2 ^ n`). -/
def Vec.ofList (l : List Zeta8) : Vec n := fun x => l.getD x.val 0

lemma Vec.ofList_toList (ψ : Vec n) : Vec.ofList (Vec.toList ψ) = ψ := by
  funext x
  simp [Vec.ofList, Vec.toList, List.getD_eq_getElem?_getD, x.isLt]

lemma Vec.toList_inj {ψ φ : Vec n} : Vec.toList ψ = Vec.toList φ ↔ ψ = φ := List.ofFn_inj

lemma Vec.map_mul_toList (a : Zeta8) (ψ : Vec n) :
    (Vec.toList ψ).map (a * ·) = Vec.toList (a • ψ) := by
  simp only [Vec.toList, List.map_ofFn, List.ofFn_inj]
  funext x
  simp

/-- Apply a circuit to a materialised state, one list per instruction. -/
def evalList (c : Circuit n) (l : List Zeta8) : List Zeta8 :=
  match c with
  | [] => l
  | g :: c => evalList c (Vec.toList (g.apply (Vec.ofList l)))

/-- The materialised evaluator agrees with `denote`. -/
lemma evalList_toList (c : Circuit n) (ψ : Vec n) :
    evalList c (Vec.toList ψ) = Vec.toList (denote c ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih => simp [evalList, Vec.ofList_toList, ih]

/-- Equivalence, as the materialised evaluator agreeing on the basis. -/
theorem equivalent_iff_evalList (c₁ c₂ : Circuit n) :
    c₁ ≡ᵤ c₂ ↔ ∀ y : Fin (2 ^ n),
      evalList c₁ (Vec.toList (basis y)) = evalList c₂ (Vec.toList (basis y)) := by
  rw [equivalent_iff_basis]
  simp only [evalList_toList, Vec.toList_inj]

/-- Equivalence up to phase, as the materialised evaluator agreeing on the
basis up to one of the eight phases. -/
theorem equivalentUpToPhase_iff_evalList (c₁ c₂ : Circuit n) :
    c₁ ≡ₚ c₂ ↔ ∃ k : Fin 8, ∀ y : Fin (2 ^ n), evalList c₁ (Vec.toList (basis y)) =
      (evalList c₂ (Vec.toList (basis y))).map (Zeta8.ω ^ (k : ℕ) * ·) := by
  rw [equivalentUpToPhase_iff_basis]
  simp only [evalList_toList, Vec.map_mul_toList, Vec.toList_inj]

/-- Equivalence of concrete circuits is decidable: run the materialised
evaluator on the `2 ^ n` basis vectors. -/
instance decidableEquivalent (c₁ c₂ : Circuit n) : Decidable (c₁ ≡ᵤ c₂) :=
  decidable_of_iff _ (equivalent_iff_evalList c₁ c₂).symm

/-- Decidable: eight candidate phases, `2 ^ n` basis vectors each. -/
instance decidableEquivalentUpToPhase (c₁ c₂ : Circuit n) : Decidable (c₁ ≡ₚ c₂) :=
  decidable_of_iff _ (equivalentUpToPhase_iff_evalList c₁ c₂).symm

end Circuit

end Quantum
