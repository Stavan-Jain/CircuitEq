/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Semantics

/-!
# The algebra of the equivalence relations

`≡ᵤ`, `≡ₚ[k]` and `≡ₚ` (`CircuitEq.Semantics`) compose the same way: `refl`,
`symm`, `trans`, `append`, `cons`; `≡ₛ` has `refl`, `symm`, `trans` and `append`
(its `cons` is `QUEUE.md` item 13). In the named form the exponents add, in
`Fin 8` and hence modulo eight, and reversing a relation negates the exponent.
`Trans` instances let one `calc` mix `≡ᵤ`, `≡ₚ[k]` and `≡ₚ` steps in any order.
-/

namespace Quantum.Circuit

variable {n : ℕ}

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

/-- Exact equivalence is equivalence with trivial scalar. -/
lemma toUpToScalar {c₁ c₂ : Circuit n} (h : c₁ ≡ᵤ c₂) : c₁ ≡ₛ c₂ :=
  ⟨1, isUnit_one, fun ψ => by simp [h ψ]⟩

/-- Exact equivalence is equivalence with the phase `ω ^ 0 = 1`. -/
lemma toWithPhase {c₁ c₂ : Circuit n} (h : c₁ ≡ᵤ c₂) : c₁ ≡ₚ[0] c₂ :=
  fun ψ => by simp [h ψ]

/-- Exact equivalence is equivalence with trivial phase. -/
lemma toUpToPhase {c₁ c₂ : Circuit n} (h : c₁ ≡ᵤ c₂) : c₁ ≡ₚ c₂ := ⟨0, h.toWithPhase⟩

/-- An exact step before a step with a named phase keeps the phase. -/
lemma trans_withPhase {k : Fin 8} {c₁ c₂ c₃ : Circuit n} (h₁ : c₁ ≡ᵤ c₂) (h₂ : c₂ ≡ₚ[k] c₃) :
    c₁ ≡ₚ[k] c₃ :=
  fun ψ => (h₁ ψ).trans (h₂ ψ)

end Equivalent

/-- `≡ₚ` says that some phase can be named. -/
theorem equivalentUpToPhase_iff_exists {c₁ c₂ : Circuit n} : c₁ ≡ₚ c₂ ↔ ∃ k, c₁ ≡ₚ[k] c₂ :=
  Iff.rfl

/-- The phase `ω ^ 0 = 1` is exact equivalence. -/
theorem equivalentWithPhase_zero_iff {c₁ c₂ : Circuit n} : c₁ ≡ₚ[0] c₂ ↔ c₁ ≡ᵤ c₂ :=
  ⟨fun h ψ => by simpa using h ψ, Equivalent.toWithPhase⟩

/-! ### The algebra of named phases

Along a chain and along a sequential composition the phases multiply, so
their exponents add in `Fin 8`; reversing a relation negates the exponent.
The lemmas about `≡ₚ` below are these with the exponent forgotten, and
`toUpToScalar`. -/

namespace EquivalentWithPhase

variable {j k : Fin 8}

/-- Every circuit is itself, with the phase `ω ^ 0 = 1`. -/
protected lemma refl (c : Circuit n) : c ≡ₚ[0] c := (Equivalent.refl c).toWithPhase

/-- Reversing the relation inverts the phase: `-k` in `Fin 8` is `8 - k`. -/
protected lemma symm {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ[k] c₂) : c₂ ≡ₚ[-k] c₁ := fun ψ => by
  rw [h ψ, smul_smul, Zeta8.ω_pow_val_neg_mul, one_smul]

/-- Along a chain the phases multiply: the exponents add modulo eight. -/
protected lemma trans {c₁ c₂ c₃ : Circuit n} (h₁ : c₁ ≡ₚ[j] c₂) (h₂ : c₂ ≡ₚ[k] c₃) :
    c₁ ≡ₚ[j + k] c₃ := fun ψ => by
  rw [h₁ ψ, h₂ ψ, smul_smul, Zeta8.ω_pow_val_add]

/-- An exact step after a step with a named phase keeps the phase. -/
lemma trans_equivalent {c₁ c₂ c₃ : Circuit n} (h₁ : c₁ ≡ₚ[k] c₂) (h₂ : c₂ ≡ᵤ c₃) :
    c₁ ≡ₚ[k] c₃ := fun ψ => by
  rw [h₁ ψ, h₂ ψ]

/-- Sequential composition multiplies the phases: a scalar passes through
the second circuit by linearity. -/
protected lemma append {c₁ c₁' c₂ c₂' : Circuit n} (h₁ : c₁ ≡ₚ[j] c₁') (h₂ : c₂ ≡ₚ[k] c₂') :
    c₁ ++ c₂ ≡ₚ[j + k] c₁' ++ c₂' := fun ψ => by
  rw [denote_append, denote_append, h₁ ψ, denote_smul, h₂, smul_smul, Zeta8.ω_pow_val_add]

/-- The same circuit appended to both sides keeps the phase. -/
lemma append_right {c₁ c₁' : Circuit n} (h : c₁ ≡ₚ[k] c₁') (c : Circuit n) :
    c₁ ++ c ≡ₚ[k] c₁' ++ c := fun ψ => by
  rw [denote_append, denote_append, h ψ, denote_smul]

/-- The same circuit prepended to both sides keeps the phase. -/
lemma append_left (c : Circuit n) {c₂ c₂' : Circuit n} (h : c₂ ≡ₚ[k] c₂') :
    c ++ c₂ ≡ₚ[k] c ++ c₂' := fun ψ => by
  rw [denote_append, denote_append, h]

/-- Prepending the same instruction keeps the phase. -/
protected lemma cons (g : Instr n) {c c' : Circuit n} (h : c ≡ₚ[k] c') : g :: c ≡ₚ[k] g :: c' :=
  fun ψ => h (g.apply ψ)

/-- Restate the phase: for an exponent that arithmetic produced, such as
`3 + 7`, `h.cast (by decide)` names it `2`. -/
protected lemma cast {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ[j] c₂) (hjk : j = k) : c₁ ≡ₚ[k] c₂ :=
  hjk ▸ h

/-- A named phase is a phase. -/
lemma toUpToPhase {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ[k] c₂) : c₁ ≡ₚ c₂ := ⟨k, h⟩

/-- The phase `ω ^ 0 = 1` is exact equivalence. -/
lemma toEquivalent {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ[0] c₂) : c₁ ≡ᵤ c₂ :=
  equivalentWithPhase_zero_iff.1 h

end EquivalentWithPhase

namespace EquivalentUpToPhase

/-- Reflexivity, with the phase `1`. -/
@[refl] protected lemma refl (c : Circuit n) : c ≡ₚ c := ⟨0, EquivalentWithPhase.refl c⟩

/-- Symmetry, with the inverse phase. -/
@[symm] protected lemma symm {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ c₂) : c₂ ≡ₚ c₁ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, hk.symm⟩

/-- Transitivity: the phases multiply. -/
@[trans] protected lemma trans {c₁ c₂ c₃ : Circuit n} (h₁ : c₁ ≡ₚ c₂) (h₂ : c₂ ≡ₚ c₃) :
    c₁ ≡ₚ c₃ := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  exact ⟨j + k, hj.trans hk⟩

/-- Equivalence up to phase is a congruence for sequential composition: the
phases of the two halves multiply. -/
protected lemma append {c₁ c₁' c₂ c₂' : Circuit n} (h₁ : c₁ ≡ₚ c₁') (h₂ : c₂ ≡ₚ c₂') :
    c₁ ++ c₂ ≡ₚ c₁' ++ c₂' := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  exact ⟨j + k, hj.append hk⟩

/-- Prepending the same instruction preserves equivalence up to phase. -/
protected lemma cons (g : Instr n) {c c' : Circuit n} (h : c ≡ₚ c') : g :: c ≡ₚ g :: c' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.cons g⟩

/-- A phase is a unit scalar. -/
lemma toUpToScalar {c₁ c₂ : Circuit n} (h : c₁ ≡ₚ c₂) : c₁ ≡ₛ c₂ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨Zeta8.ω ^ (k : ℕ), isUnit_ω.pow _, hk⟩

end EquivalentUpToPhase

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

/-! `calc` support for phases. A chain may mix `≡ᵤ`, `≡ₚ[k]` and `≡ₚ` steps
in any order. Exact steps leave a named phase alone, two named phases add
(`≡ₚ[j]` then `≡ₚ[k]` is `≡ₚ[j + k]`, and a goal stated with the numeral
closes by unification, since `Fin 8` arithmetic on numerals computes), and
as soon as one step is `≡ₚ` the chain is. -/

/-- `calc` support: `≡ᵤ` then `≡ₚ`. -/
instance : @Trans (Circuit n) (Circuit n) (Circuit n)
    Equivalent EquivalentUpToPhase EquivalentUpToPhase :=
  ⟨fun h₁ h₂ => h₁.toUpToPhase.trans h₂⟩

/-- `calc` support: `≡ₚ` then `≡ᵤ`. -/
instance : @Trans (Circuit n) (Circuit n) (Circuit n)
    EquivalentUpToPhase Equivalent EquivalentUpToPhase :=
  ⟨fun h₁ h₂ => h₁.trans h₂.toUpToPhase⟩

/-- `calc` support: `≡ₚ` then `≡ₚ`. -/
instance : @Trans (Circuit n) (Circuit n) (Circuit n)
    EquivalentUpToPhase EquivalentUpToPhase EquivalentUpToPhase :=
  ⟨EquivalentUpToPhase.trans⟩

/-- `calc` support: `≡ᵤ` then `≡ₚ[k]` is `≡ₚ[k]`. -/
instance {k : Fin 8} : @Trans (Circuit n) (Circuit n) (Circuit n)
    Equivalent (EquivalentWithPhase k) (EquivalentWithPhase k) :=
  ⟨Equivalent.trans_withPhase⟩

/-- `calc` support: `≡ₚ[k]` then `≡ᵤ` is `≡ₚ[k]`. -/
instance {k : Fin 8} : @Trans (Circuit n) (Circuit n) (Circuit n)
    (EquivalentWithPhase k) Equivalent (EquivalentWithPhase k) :=
  ⟨EquivalentWithPhase.trans_equivalent⟩

/-- `calc` support: `≡ₚ[j]` then `≡ₚ[k]` is `≡ₚ[j + k]`. -/
instance {j k : Fin 8} : @Trans (Circuit n) (Circuit n) (Circuit n)
    (EquivalentWithPhase j) (EquivalentWithPhase k) (EquivalentWithPhase (j + k)) :=
  ⟨EquivalentWithPhase.trans⟩

/-- `calc` support: `≡ₚ[k]` then `≡ₚ`. -/
instance {k : Fin 8} : @Trans (Circuit n) (Circuit n) (Circuit n)
    (EquivalentWithPhase k) EquivalentUpToPhase EquivalentUpToPhase :=
  ⟨fun h₁ h₂ => h₁.toUpToPhase.trans h₂⟩

/-- `calc` support: `≡ₚ` then `≡ₚ[k]`. -/
instance {k : Fin 8} : @Trans (Circuit n) (Circuit n) (Circuit n)
    EquivalentUpToPhase (EquivalentWithPhase k) EquivalentUpToPhase :=
  ⟨fun h₁ h₂ => h₁.trans h₂.toUpToPhase⟩

end Quantum.Circuit
