/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Gates
import CircuitEq.Dyadic
import CircuitEq.Chunk
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

The instances evaluate through `evalFn`, a closure evaluator over the
gcd-free coefficients `Dyadic8` (`CircuitEq.Dyadic`) on `ℕ`-indexed states,
proved equal to `denote` (`toZeta8_evalFn`), so the kernel's cost is linear
in depth, one memoised step per amplitude and gate, and its arithmetic is
integer arithmetic. `evalList` is the materialised list-backed evaluator
over `Zeta8`, proved equal to `denote` (`evalList_toList`), and `evalListD`
its dyadic form, proved equal to it (`map_toZeta8_evalListD`); they are the
reference forms. `denote` itself is nested closures over `Fin`, which the
kernel cannot memoise.

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

/-- Equivalence up to a global scalar that is a unit of the coefficient
ring. For unitaries the scalar has modulus one, and for Clifford+T it is a
power of `ω`, but that is a theorem about the ring rather than part of the
definition; this is the relation a Clifford tableau certifies. -/
def EquivalentUpToScalar (c₁ c₂ : Circuit n) : Prop :=
  ∃ a : Zeta8, IsUnit a ∧ ∀ ψ : Vec n, denote c₁ ψ = a • denote c₂ ψ

@[inherit_doc] scoped infix:50 " ≡ₛ " => EquivalentUpToScalar

/-- `ω` is a unit: `ω · ω⁷ = 1`. -/
lemma isUnit_ω : IsUnit Zeta8.ω :=
  ⟨⟨Zeta8.ω, Zeta8.ω ^ 7, by decide +kernel, by decide +kernel⟩, rfl⟩

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

/-- Exact equivalence is equivalence with trivial scalar. -/
lemma toUpToScalar {c₁ c₂ : Circuit n} (h : c₁ ≡ᵤ c₂) : c₁ ≡ₛ c₂ :=
  ⟨1, isUnit_one, fun ψ => by simp [h ψ]⟩

end Equivalent

/-- A phase is a unit scalar. -/
lemma EquivalentUpToPhase.toUpToScalar {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ c₂) : c₁ ≡ₛ c₂ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨Zeta8.ω ^ (k : ℕ), isUnit_ω.pow _, hk⟩

namespace EquivalentUpToScalar

@[refl] protected lemma refl (c : Circuit n) : c ≡ₛ c :=
  ⟨1, isUnit_one, fun _ => (one_smul _ _).symm⟩

@[symm] protected lemma symm {c₁ c₂ : Circuit n} (h : c₁ ≡ₛ c₂) : c₂ ≡ₛ c₁ := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨↑ha.unit⁻¹, (ha.unit⁻¹).isUnit, fun ψ => ?_⟩
  rw [h ψ, smul_smul, Units.inv_mul_of_eq ha.unit_spec, one_smul]

@[trans] protected lemma trans {c₁ c₂ c₃ : Circuit n} (h₁ : c₁ ≡ₛ c₂) (h₂ : c₂ ≡ₛ c₃) :
    c₁ ≡ₛ c₃ := by
  obtain ⟨a, ha, h₁⟩ := h₁
  obtain ⟨b, hb, h₂⟩ := h₂
  exact ⟨a * b, ha.mul hb, fun ψ => by rw [h₁ ψ, h₂ ψ, smul_smul]⟩

/-- Equivalence up to scalar is a congruence for sequential composition. -/
protected lemma append {c₁ c₁' c₂ c₂' : Circuit n} (h₁ : c₁ ≡ₛ c₁') (h₂ : c₂ ≡ₛ c₂') :
    c₁ ++ c₂ ≡ₛ c₁' ++ c₂' := by
  obtain ⟨a, ha, h₁⟩ := h₁
  obtain ⟨b, hb, h₂⟩ := h₂
  refine ⟨a * b, ha.mul hb, fun ψ => ?_⟩
  rw [denote_append, denote_append, h₁ ψ, denote_smul, h₂, smul_smul]

end EquivalentUpToScalar

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

/-! ### The dyadic evaluator

`evalList` is the semantic reference, but its arithmetic is `Zeta8`: four
rationals normalised by a gcd on every operation, which is where the kernel
spends its time. `evalListD` is the same evaluator over `Dyadic8`
(`CircuitEq.Dyadic`), integer numerators over a power of `√2` with no gcd
and no division. `map_toZeta8_evalListD` is the correspondence, `eqvList`
compares two dyadic states exactly (`eqvList_iff`), and
`equivalent_iff_evalListD` is the basis decision in this form. It is the
materialised reference; the `Decidable` instances run the closure form of
the next section, which is faster and lighter for the kernel. -/

/-- The dyadic action of one instruction: the per-gate shuffle
`Gate1.applyD`, or the CNOT permutation. -/
def Instr.applyD : Instr n → VecD n → VecD n
  | .one g i => g.applyD i
  | .cnot c t => applyCNOTD c t

/-- `Instr.applyD` means `Instr.apply`. -/
lemma Instr.toZeta8_comp_applyD (g : Instr n) (ψ : VecD n) :
    Dyadic8.toZeta8 ∘ g.applyD ψ = g.apply (Dyadic8.toZeta8 ∘ ψ) := by
  cases g with
  | one g i => simp only [Instr.applyD, Instr.apply_one, Gate1.toZeta8_comp_applyD]
  | cnot c t => exact toZeta8_comp_applyCNOTD c t ψ

/-- A dyadic state as its list of amplitudes: entry `x` is `ψ x`. -/
def VecD.toList (ψ : VecD n) : List Dyadic8 := List.ofFn ψ

/-- A list of dyadic amplitudes as a state (`zero` past the end, which does
not happen for lists of length `2 ^ n`). -/
def VecD.ofList (l : List Dyadic8) : VecD n := fun x => l.getD x.val Dyadic8.zero

/-- `VecD.toList` means `Vec.toList`. -/
lemma VecD.map_toZeta8_toList (ψ : VecD n) :
    (VecD.toList ψ).map Dyadic8.toZeta8 = Vec.toList (Dyadic8.toZeta8 ∘ ψ) := by
  simp [VecD.toList, Vec.toList, List.map_ofFn]

/-- `VecD.ofList` means `Vec.ofList`. -/
lemma VecD.toZeta8_comp_ofList (l : List Dyadic8) :
    Dyadic8.toZeta8 ∘ (VecD.ofList l : VecD n) = Vec.ofList (l.map Dyadic8.toZeta8) := by
  funext x
  simp only [Function.comp_apply, VecD.ofList, Vec.ofList, List.getD_eq_getElem?_getD,
    List.getElem?_map, ← Dyadic8.toZeta8_zero, Option.getD_map]

/-- Apply a circuit to a materialised dyadic state, one list per instruction. -/
def evalListD (c : Circuit n) (l : List Dyadic8) : List Dyadic8 :=
  match c with
  | [] => l
  | g :: c => evalListD c (VecD.toList (g.applyD (VecD.ofList l)))

/-- The dyadic evaluator means the `Zeta8` one. -/
lemma map_toZeta8_evalListD (c : Circuit n) (l : List Dyadic8) :
    (evalListD c l).map Dyadic8.toZeta8 = evalList c (l.map Dyadic8.toZeta8) := by
  induction c generalizing l with
  | nil => rfl
  | cons g c ih =>
    simp only [evalListD, evalList, ih, VecD.map_toZeta8_toList, Instr.toZeta8_comp_applyD,
      VecD.toZeta8_comp_ofList]

/-- The computational-basis vector `|y⟩`, dyadic. -/
def basisD (y : Fin (2 ^ n)) : VecD n := fun x => if x = y then Dyadic8.one else Dyadic8.zero

/-- `basisD` means `basis`. -/
lemma toZeta8_comp_basisD (y : Fin (2 ^ n)) : Dyadic8.toZeta8 ∘ basisD y = basis y := by
  funext x
  simp only [Function.comp_apply, basisD, basis]
  split_ifs <;> simp

/-- Exact equality of two dyadic amplitude lists, entry by entry. -/
def eqvList : List Dyadic8 → List Dyadic8 → Bool
  | [], [] => true
  | x :: l, y :: m => Dyadic8.eqv x y && eqvList l m
  | _, _ => false

/-- `eqvList` decides equality of the denoted amplitude lists. -/
lemma eqvList_iff (l m : List Dyadic8) :
    eqvList l m = true ↔ l.map Dyadic8.toZeta8 = m.map Dyadic8.toZeta8 := by
  induction l generalizing m with
  | nil => cases m <;> simp [eqvList]
  | cons x l ih =>
    cases m with
    | nil => simp [eqvList]
    | cons y m => simp [eqvList, Dyadic8.eqv_iff, ih]

/-- Equivalence, as the dyadic evaluator agreeing on the basis. -/
theorem equivalent_iff_evalListD (c₁ c₂ : Circuit n) :
    c₁ ≡ᵤ c₂ ↔ ∀ y : Fin (2 ^ n),
      eqvList (evalListD c₁ (VecD.toList (basisD y)))
        (evalListD c₂ (VecD.toList (basisD y))) = true := by
  rw [equivalent_iff_evalList]
  simp only [eqvList_iff, map_toZeta8_evalListD, VecD.map_toZeta8_toList, toZeta8_comp_basisD]

/-- Scaling a dyadic list by `ωPow k` means scaling its meaning by `ω ^ k`. -/
lemma map_toZeta8_map_mul_ωPow (k : ℕ) (l : List Dyadic8) :
    (l.map (Dyadic8.mul (Dyadic8.ωPow k))).map Dyadic8.toZeta8 =
      (l.map Dyadic8.toZeta8).map (Zeta8.ω ^ k * ·) := by
  simp [List.map_map, Function.comp_def, Dyadic8.toZeta8_mul, Dyadic8.toZeta8_ωPow]

/-- Equivalence up to phase, as the dyadic evaluator agreeing on the basis up
to one of the eight phases, applied on the dyadic side. -/
theorem equivalentUpToPhase_iff_evalListD (c₁ c₂ : Circuit n) :
    c₁ ≡ₚ c₂ ↔ ∃ k : Fin 8, ∀ y : Fin (2 ^ n),
      eqvList (evalListD c₁ (VecD.toList (basisD y)))
        ((evalListD c₂ (VecD.toList (basisD y))).map
          (Dyadic8.mul (Dyadic8.ωPow (k : ℕ)))) = true := by
  rw [equivalentUpToPhase_iff_evalList]
  simp only [eqvList_iff, map_toZeta8_map_mul_ωPow, map_toZeta8_evalListD,
    VecD.map_toZeta8_toList, toZeta8_comp_basisD]

/-! ### The closure evaluator the instances run

`evalListD` materialises a list per instruction, and reading amplitude `x`
of a list takes `x` steps, so a gate costs `O(4 ^ n)` and the kernel retains
every intermediate term of every read. `evalFn` instead composes the
`ℕ`-indexed gate actions of `CircuitEq.Dyadic` as closures. The kernel
memoises `whnf` by structural equality of terms, so a read `ψ x` at a
numeral `x` is one cache lookup once computed, a gate costs `O(2 ^ n)`, and
nothing is retained beyond the amplitudes themselves. (Over `Fin` the same
closures recompute exponentially, because the index carries a proof term;
see `CircuitEq.Dyadic`.) Its meaning is `denote` on the indices below
`2 ^ n` (`toZeta8_evalFn`), and `checkEquiv` and `checkEquivUpToPhase` are
the `Bool` loops the `Decidable` instances reduce to. -/

/-- The `ℕ`-indexed dyadic action of one instruction. -/
def Instr.applyN : Instr n → VecN → VecN
  | .one g i => g.applyN i
  | .cnot c t => applyCNOTN c t

/-- On indices below `2 ^ n`, `Instr.applyN` is `Instr.applyD`. -/
lemma Instr.applyN_val (g : Instr n) (ψ : VecN) (x : Fin (2 ^ n)) :
    g.applyN ψ x = g.applyD (ψ ∘ Fin.val) x := by
  cases g with
  | one g i => exact Gate1.applyN_val g i ψ x
  | cnot c t => exact applyCNOTN_val c t ψ x

/-- The closure evaluator: compose the instructions' actions on an
`ℕ`-indexed state. -/
def evalFn : Circuit n → VecN → VecN
  | [], ψ => ψ
  | g :: c, ψ => evalFn c (g.applyN ψ)

/-- `evalFn` means `denote` on the indices below `2 ^ n`. -/
lemma toZeta8_evalFn (c : Circuit n) (ψ : VecN) {x : ℕ} (hx : x < 2 ^ n) :
    Dyadic8.toZeta8 (evalFn c ψ x) = denote c (Dyadic8.toZeta8 ∘ ψ ∘ Fin.val) ⟨x, hx⟩ := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih =>
    rw [evalFn, denote_cons, ih]
    congr 1
    funext z
    rw [Function.comp_apply, Function.comp_apply, Instr.applyN_val]
    exact congrFun (Instr.toZeta8_comp_applyD g (ψ ∘ Fin.val)) z

/-- The computational-basis vector `|y⟩` on `ℕ` indices. -/
def basisN (y : ℕ) : VecN := fun x => if x = y then Dyadic8.one else Dyadic8.zero

/-- `basisN` means `basis` on the indices below `2 ^ n`. -/
lemma toZeta8_comp_basisN {y : ℕ} (hy : y < 2 ^ n) :
    Dyadic8.toZeta8 ∘ basisN y ∘ Fin.val = basis (n := n) ⟨y, hy⟩ := by
  funext x
  simp only [Function.comp_apply, basisN, basis, Fin.ext_iff]
  split_ifs <;> simp

/-- The basis decision as one `Bool`: for every basis state and every
amplitude, the two closure evaluations agree. -/
def checkEquiv (c₁ c₂ : Circuit n) : Bool :=
  (List.range (2 ^ n)).all fun y =>
    (List.range (2 ^ n)).all fun x =>
      Dyadic8.eqv ((evalFn c₁ (basisN y)).at x) ((evalFn c₂ (basisN y)).at x)

/-- `checkEquiv` decides `≡ᵤ`. -/
theorem checkEquiv_iff (c₁ c₂ : Circuit n) : checkEquiv c₁ c₂ = true ↔ c₁ ≡ᵤ c₂ := by
  rw [equivalent_iff_basis, checkEquiv]
  simp only [List.all_eq_true, List.mem_range, Dyadic8.eqv_iff, VecN.at_eq]
  constructor
  · intro h y
    funext x
    have := h y.val y.isLt x.val x.isLt
    rwa [toZeta8_evalFn _ _ x.isLt, toZeta8_evalFn _ _ x.isLt, toZeta8_comp_basisN y.isLt] at this
  · intro h y hy x hx
    rw [toZeta8_evalFn _ _ hx, toZeta8_evalFn _ _ hx, toZeta8_comp_basisN hy, h]

/-- The basis decision up to phase as one `Bool`: eight candidate phases,
applied on the dyadic side. -/
def checkEquivUpToPhase (c₁ c₂ : Circuit n) : Bool :=
  (List.range 8).any fun k =>
    (List.range (2 ^ n)).all fun y =>
      (List.range (2 ^ n)).all fun x =>
        Dyadic8.eqv ((evalFn c₁ (basisN y)).at x)
          (Dyadic8.mul (Dyadic8.ωPow k) ((evalFn c₂ (basisN y)).at x))

/-- `checkEquivUpToPhase` decides `≡ₚ`. -/
theorem checkEquivUpToPhase_iff (c₁ c₂ : Circuit n) :
    checkEquivUpToPhase c₁ c₂ = true ↔ c₁ ≡ₚ c₂ := by
  rw [equivalentUpToPhase_iff_basis, checkEquivUpToPhase]
  simp only [List.any_eq_true, List.all_eq_true, List.mem_range, Dyadic8.eqv_iff,
    Dyadic8.toZeta8_mul, Dyadic8.toZeta8_ωPow, VecN.at_eq]
  constructor
  · rintro ⟨k, hk, h⟩
    refine ⟨⟨k, hk⟩, fun y => ?_⟩
    funext x
    have := h y.val y.isLt x.val x.isLt
    rw [toZeta8_evalFn _ _ x.isLt, toZeta8_evalFn _ _ x.isLt, toZeta8_comp_basisN y.isLt] at this
    exact this
  · rintro ⟨k, h⟩
    refine ⟨k.val, k.isLt, fun y hy x hx => ?_⟩
    rw [toZeta8_evalFn _ _ hx, toZeta8_evalFn _ _ hx, toZeta8_comp_basisN hy, h]
    rfl

/-! ### The chunked basis decision

`checkEquiv` evaluates all `2 ^ n` basis vectors inside one declaration, and
the kernel keeps every memoised amplitude until that declaration ends, so
memory runs out at seven qubits. `checkEquivAt` is the check on one basis
vector; a file proves it on ranges of basis vectors, one declaration per
range, and `equivalent_of_allBelow` assembles them (`CircuitEq.Chunk`). -/

/-- The basis decision on the basis vector `|y⟩` alone: every amplitude of
the two closure evaluations agrees. -/
def checkEquivAt (c₁ c₂ : Circuit n) (y : ℕ) : Bool :=
  (List.range (2 ^ n)).all fun x =>
    Dyadic8.eqv ((evalFn c₁ (basisN y)).at x) ((evalFn c₂ (basisN y)).at x)

/-- `checkEquiv` is `checkEquivAt` on every basis vector. -/
lemma checkEquiv_eq_all (c₁ c₂ : Circuit n) :
    checkEquiv c₁ c₂ = (List.range (2 ^ n)).all (checkEquivAt c₁ c₂) := rfl

/-- The chunked basis decision: `checkEquivAt` on every basis vector,
proved a range at a time, gives `≡ᵤ`. -/
theorem equivalent_of_allBelow {c₁ c₂ : Circuit n}
    (h : AllBelow (checkEquivAt c₁ c₂) (2 ^ n)) : c₁ ≡ᵤ c₂ :=
  (checkEquiv_iff c₁ c₂).1 (by rw [checkEquiv_eq_all]; exact h.all_range)

/-- The basis decision up to the phase `ω ^ k` on the basis vector `|y⟩`
alone. -/
def checkEquivUpToPhaseAt (c₁ c₂ : Circuit n) (k y : ℕ) : Bool :=
  (List.range (2 ^ n)).all fun x =>
    Dyadic8.eqv ((evalFn c₁ (basisN y)).at x)
      (Dyadic8.mul (Dyadic8.ωPow k) ((evalFn c₂ (basisN y)).at x))

/-- The chunked basis decision up to a phase: one phase `ω ^ k`, named by
the file, on every basis vector gives `≡ₚ`. -/
theorem equivalentUpToPhase_of_allBelow {c₁ c₂ : Circuit n} {k : ℕ} (hk : k < 8)
    (h : AllBelow (checkEquivUpToPhaseAt c₁ c₂ k) (2 ^ n)) : c₁ ≡ₚ c₂ := by
  rw [← checkEquivUpToPhase_iff, checkEquivUpToPhase, List.any_eq_true]
  exact ⟨k, List.mem_range.2 hk, h.all_range⟩

/-- Equivalence of concrete circuits is decidable: run the closure
evaluator on the `2 ^ n` basis vectors. -/
instance decidableEquivalent (c₁ c₂ : Circuit n) : Decidable (c₁ ≡ᵤ c₂) :=
  decidable_of_iff _ (checkEquiv_iff c₁ c₂)

/-- Decidable: eight candidate phases, `2 ^ n` basis vectors each. -/
instance decidableEquivalentUpToPhase (c₁ c₂ : Circuit n) : Decidable (c₁ ≡ₚ c₂) :=
  decidable_of_iff _ (checkEquivUpToPhase_iff c₁ c₂)

end Circuit

end Quantum
