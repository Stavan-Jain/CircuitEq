/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Structural
import CircuitEq.Support
import Mathlib.Data.List.Perm.Basic

/-! # Rewriting circuits and commuting blocks

All rules act on circuit equivalence. `Instr.CanCommute` is a conservative,
decidable sufficient condition, not a characterization of commutation.
-/

namespace Quantum.Circuit

open Instr
variable {n : ℕ}

/-- Replace an equivalent window inside an unchanged prefix and suffix. -/
theorem Equivalent.in_context {a b : Circuit n} (h : a ≡ᵤ b)
    (pre post : Circuit n) : pre ++ a ++ post ≡ᵤ pre ++ b ++ post :=
  ((Equivalent.refl pre).append h).append (Equivalent.refl post)

/-- CNOTs commute unless a control is the other gate's target. -/
theorem cnot_cnot_comm {a b c d : Fin n} (had : a ≠ d) (hcb : c ≠ b) :
    [CX a b, CX c d] ≡ᵤ [CX c d, CX a b] :=
  fun ψ => applyCNOT_comm hcb had ψ

/-- Moving two Hadamards across a CNOT reverses its direction. -/
theorem cnot_hadamards_reverse {c t : Fin n} (h : c ≠ t) :
    [CX c t, H c, H t] ≡ᵤ [H c, H t, CX t c] :=
  applyHadamards_applyCNOT h

/-- A decidable sufficient condition for swapping two instructions: equal
gates; gates on disjoint wires; two diagonal gates on one wire; a diagonal
gate on the control of a CNOT; `X` on the target of a CNOT; two CNOTs
neither of whose controls is the other's target. -/
def Instr.CanCommute (a b : Instr n) : Prop :=
  a = b ∨ match a, b with
    | .one g i, .one g' j => i ≠ j ∨ (g.isDiag ∧ g'.isDiag)
    | .one g i, .cnot c t =>
      (i ≠ c ∧ i ≠ t) ∨ (c ≠ t ∧ ((i = c ∧ g.isDiag) ∨ (i = t ∧ g = .X)))
    | .cnot c t, .one g i =>
      (i ≠ c ∧ i ≠ t) ∨ (c ≠ t ∧ ((i = c ∧ g.isDiag) ∨ (i = t ∧ g = .X)))
    | .cnot a b, .cnot c d => a ≠ d ∧ c ≠ b

instance (a b : Instr n) : Decidable (a.CanCommute b) := by
  unfold Instr.CanCommute
  cases a <;> cases b <;> infer_instance

/-- Two diagonal gates on one wire commute. -/
lemma diag_diag_comm {A B : Gate1} (hA : A.isDiag = true) (hB : B.isDiag = true) (i : Fin n) :
    [Instr.one A i, Instr.one B i] ≡ᵤ [Instr.one B i, Instr.one A i] := by
  intro ψ
  simp only [denote_cons, denote_nil, Instr.apply_one, applyOne_applyOne_same]
  rw [Gate1.mat_comm_of_isDiag hB hA]

/-- `X` on the target commutes with a CNOT. -/
lemma cnot_X_target_comm {c t : Fin n} (hct : c ≠ t) :
    [Instr.one .X t, Instr.cnot c t] ≡ᵤ [Instr.cnot c t, Instr.one .X t] :=
  fun ψ => applyCNOT_applyOne_X_target_comm hct ψ

/-- The single-qubit-versus-CNOT half of `Instr.CanCommute.sound`. -/
lemma one_cnot_comm_of_check {A : Gate1} {i c t : Fin n}
    (h : (i ≠ c ∧ i ≠ t) ∨ (c ≠ t ∧ ((i = c ∧ A.isDiag) ∨ (i = t ∧ A = .X)))) :
    [Instr.one A i, Instr.cnot c t] ≡ᵤ [Instr.cnot c t, Instr.one A i] := by
  rcases h with ⟨hc, ht⟩ | ⟨hct, ⟨rfl, hA⟩ | ⟨rfl, rfl⟩⟩
  · exact fun ψ => (applyOne_applyCNOT_comm hc ht A.mat ψ).symm
  · exact cnot_diag_control_comm hct (Gate1.mat_off_diag_of_isDiag hA)
  · exact cnot_X_target_comm hct

/-- The syntactic commutation check produces a semantic circuit identity. -/
theorem Instr.CanCommute.sound {a b : Instr n} (h : a.CanCommute b) :
    [a, b] ≡ᵤ [b, a] := by
  rcases h with h | h
  · subst b; exact Equivalent.refl _
  · cases a with
    | one A i =>
      cases b with
      | one B j =>
        rcases h with h | ⟨hA, hB⟩
        · exact one_one_comm h A B
        · by_cases hij : i = j
          · subst hij; exact diag_diag_comm hA hB i
          · exact one_one_comm hij A B
      | cnot c t => exact one_cnot_comm_of_check h
    | cnot c t =>
      cases b with
      | one A i => exact (one_cnot_comm_of_check h).symm
      | cnot d u => exact cnot_cnot_comm h.1 h.2

/-- Instructions that share no wire pass the commutation check. -/
lemma Instr.CanCommute.of_no_shared_wire {a b : Instr n}
    (h : ∀ i, ¬ (a.touches i ∧ b.touches i)) : a.CanCommute b := by
  refine Or.inr ?_
  cases a with
  | one g i =>
    cases b with
    | one g' j => exact Or.inl fun e => h i ⟨rfl, e.symm⟩
    | cnot c t =>
      exact Or.inl ⟨fun e => h i ⟨rfl, Or.inl e.symm⟩,
        fun e => h i ⟨rfl, Or.inr e.symm⟩⟩
  | cnot c t =>
    cases b with
    | one g i =>
      exact Or.inl ⟨fun e => h i ⟨Or.inl e.symm, rfl⟩,
        fun e => h i ⟨Or.inr e.symm, rfl⟩⟩
    | cnot d u =>
      exact ⟨fun e => h c ⟨Or.inl rfl, Or.inr e.symm⟩,
        fun e => h t ⟨Or.inr rfl, Or.inl e⟩⟩

/-- Instructions with disjoint supports commute. -/
lemma Instr.CanCommute.of_disjoint {a b : Instr n} (h : a.support &&& b.support = 0) :
    a.CanCommute b :=
  Instr.CanCommute.of_no_shared_wire (Instr.not_touches_both_of_disjoint h)

/-- `g` passes the syntactic commutation check against every instruction
of `c`: the side condition the tactics discharge by `decide`. -/
def Instr.CanCommuteAll (g : Instr n) (c : Circuit n) : Prop := ∀ a ∈ c, g.CanCommute a

instance (g : Instr n) (c : Circuit n) : Decidable (g.CanCommuteAll c) :=
  inferInstanceAs (Decidable (∀ a ∈ c, g.CanCommute a))

/-- Move an instruction through a block when it commutes with every gate. -/
theorem gate_block_comm (g : Instr n) (c : Circuit n)
    (h : ∀ a ∈ c, [g, a] ≡ᵤ [a, g]) : [g] ++ c ≡ᵤ c ++ [g] := by
  induction c with
  | nil => exact Equivalent.refl _
  | cons a c ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    exact (ha.in_context [] c).trans (hc.cons a)

/-- A gate whose support is disjoint from a block's commutes past the
block; the mask form of `gate_block_comm`. -/
theorem gate_block_comm_of_disjoint (g : Instr n) (c : Circuit n)
    (h : g.support &&& support c = 0) : [g] ++ c ≡ᵤ c ++ [g] := by
  apply gate_block_comm
  intro a ha
  apply Instr.CanCommute.sound
  apply Instr.CanCommute.of_no_shared_wire
  rintro i ⟨hg, ha'⟩
  have hi : g.support.testBit i.val = true := by
    rw [Instr.support_testBit]
    simpa using hg
  exact not_touches_of_disjoint h hi a ha ha'

/-- Move two blocks past each other using pairwise gate commutation. -/
theorem blocks_comm (a b : Circuit n)
    (h : ∀ x ∈ a, ∀ y ∈ b, [x, y] ≡ᵤ [y, x]) : a ++ b ≡ᵤ b ++ a := by
  induction a with
  | nil => simpa using Equivalent.refl b
  | cons g a ih =>
    have hg := gate_block_comm g b (h g (by simp))
    have ha := ih (fun x hx => h x (by simp [hx]))
    simpa [List.append_assoc] using
      (ha.cons g).trans (hg.in_context [] a)

/-- Reorder a block whose instructions commute pairwise. -/
theorem perm_equivalent {a b : Circuit n} (hp : a.Perm b)
    (hc : ∀ x ∈ a, ∀ y ∈ a, [x, y] ≡ᵤ [y, x]) : a ≡ᵤ b := by
  induction hp with
  | nil => exact Equivalent.refl _
  | cons g hp ih =>
    exact (ih (fun x hx y hy => hc x (by simp [hx]) y (by simp [hy]))).cons g
  | swap x y l => exact (hc y (by simp) x (by simp)).in_context [] l
  | trans hp hq ihp ihq =>
    exact (ihp hc).trans (ihq (fun x hx y hy => hc x (hp.mem_iff.mpr hx) y
      (hp.mem_iff.mpr hy)))

/-- A computable permutation check plus syntactic commutation suffices. -/
theorem perm_equivalent_of_check {a b : Circuit n} (hp : a.Perm b)
    (hc : ∀ x ∈ a, ∀ y ∈ a, x.CanCommute y) : a ≡ᵤ b :=
  perm_equivalent hp (fun x hx y hy => (hc x hx y hy).sound)

/-- Pull a selected instruction to the front, then prove the remaining tail. -/
theorem pull_cons (g : Instr n) (before after target : Circuit n)
    (hc : g.CanCommuteAll before) (ht : before ++ after ≡ᵤ target) :
    before ++ g :: after ≡ᵤ g :: target := by
  have hm := (gate_block_comm g before (fun a ha => (hc a ha).sound)).symm
  simpa [List.append_assoc] using (hm.in_context [] after).trans (ht.cons g)

/-- The order of identical single-qubit gates within a layer is immaterial. -/
theorem layer_perm (g : Gate1) {a b : List (Fin n)} (h : a.Perm b) :
    layer g a ≡ᵤ layer g b := by
  apply perm_equivalent (h.map (Instr.one g))
  intro x hx y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  by_cases hij : i = j
  · subst j; exact Equivalent.refl _
  · exact one_one_comm hij g g

/-- The inverse single-qubit gate in the supported alphabet. -/
def Gate1.inverse : Gate1 → Gate1
  | .H => .H | .X => .X | .Y => .Y | .Z => .Z
  | .S => .Sdg | .Sdg => .S | .T => .Tdg | .Tdg => .T

/-- Each alphabet inverse cancels its gate as a two-by-two matrix. -/
theorem Gate1.inverse_mul (g : Gate1) : g.inverse.mat * g.mat = 1 := by
  cases g <;> decide +kernel

/-- A decidable sufficient condition for cancelling two instructions. -/
def Instr.CanCancel (a b : Instr n) : Prop :=
  match a, b with
  | .one A i, .one B j => i = j ∧ B = A.inverse
  | .cnot c t, .cnot d u => c = d ∧ t = u ∧ c ≠ t
  | _, _ => False

instance (a b : Instr n) : Decidable (a.CanCancel b) := by
  unfold Instr.CanCancel
  cases a <;> cases b <;> infer_instance

/-- Checked inverse pairs cancel in every register size. -/
theorem Instr.CanCancel.sound {a b : Instr n} (h : a.CanCancel b) : [a, b] ≡ᵤ [] := by
  cases a with
  | one A i =>
    cases b with
    | one B j =>
      obtain ⟨rfl, rfl⟩ := h
      exact cancel_of_mul_eq_one A.inverse_mul i
    | cnot c t => exact h.elim
  | cnot c t =>
    cases b with
    | one A i => exact h.elim
    | cnot d u =>
      obtain ⟨rfl, rfl, hct⟩ := h
      exact applyCNOT_applyCNOT_self hct

/-- Cancel inverse gates separated by a block they can commute through. -/
theorem cancel_window (a b : Instr n) (middle tail : Circuit n)
    (hc : a.CanCancel b) (hm : a.CanCommuteAll middle) :
    a :: (middle ++ b :: tail) ≡ᵤ middle ++ tail := by
  have move := gate_block_comm a middle (fun g hg => (hm g hg).sound)
  calc
    _ ≡ᵤ (middle ++ [a, b]) ++ tail := by
      simpa [List.append_assoc] using move.in_context [] (b :: tail)
    _ ≡ᵤ middle ++ tail := by simpa using hc.sound.in_context middle tail

end Quantum.Circuit
