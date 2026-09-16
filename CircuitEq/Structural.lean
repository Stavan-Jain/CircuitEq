/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Semantics
import Mathlib.Data.List.FinRange

/-!
# Structural rewriting toolkit

Lemmas about `≡ᵤ` that hold for every qubit count `n`, phrased so that a
proof of a parametric equivalence can be assembled from them plus `2 × 2`
matrix facts decided by the kernel:

- **fusion** (`fuse`, `fuse₃`, `cancel_of_mul_eq_one`): adjacent gates on the
  same qubit collapse to one gate, or vanish, according to a matrix product;
- **commutation** (`one_one_comm`, `cnot_diag_control_comm`): gates on
  disjoint qubits commute, and diagonal gates commute through a CNOT on its
  control;
- **moving** (`denote_applyOne_comm_of_not_touches`): a single-qubit gate
  moves past any circuit that never touches its qubit;
- **layers** (`layer_layer_cancel`, `hLayer_hLayer`): a layer of an
  involutive gate on distinct qubits cancels against itself, for every `n`.

This is the vocabulary a proof-search agent is meant to speak; `decide` is
the leaf oracle, these lemmas are the connectives.
-/

namespace Quantum.Circuit

variable {n : ℕ}

/-! ### Fusion on a single qubit -/

/-- Two gates on one qubit fuse to the product (later gate on the left). -/
theorem fuse {A B C : Gate1} (h : B.mat * A.mat = C.mat) (i : Fin n) :
    [Instr.one A i, Instr.one B i] ≡ᵤ [Instr.one C i] := by
  intro ψ
  simp [applyOne_applyOne_same, h]

/-- Three gates on one qubit fuse to the product. -/
theorem fuse₃ {A B C D : Gate1} (h : C.mat * B.mat * A.mat = D.mat) (i : Fin n) :
    [Instr.one A i, Instr.one B i, Instr.one C i] ≡ᵤ [Instr.one D i] := by
  intro ψ
  simp [applyOne_applyOne_same, ← mul_assoc, h]

/-- Two gates on one qubit whose product is the identity cancel. -/
theorem cancel_of_mul_eq_one {A B : Gate1} (h : B.mat * A.mat = 1) (i : Fin n) :
    [Instr.one A i, Instr.one B i] ≡ᵤ [] := by
  intro ψ
  simp [applyOne_applyOne_same, h, applyOne_one]

/-! ### Commutation -/

/-- Single-qubit gates on distinct qubits commute. -/
theorem one_one_comm {i j : Fin n} (h : i ≠ j) (A B : Gate1) :
    [Instr.one A i, Instr.one B j] ≡ᵤ [Instr.one B j, Instr.one A i] :=
  fun ψ => applyOne_comm h.symm B.mat A.mat ψ

/-- A diagonal single-qubit matrix acts by scaling each amplitude. -/
lemma applyOne_of_diag {G : Mat1} (hG : ∀ b, G b (!b) = 0) (i : Fin n) (ψ : Vec n) (x) :
    applyOne G i ψ x = G (bit i x) (bit i x) * ψ x := by
  simp [applyOne, hG]

/-- A diagonal gate on the control commutes through a CNOT. -/
lemma applyCNOT_applyOne_control_comm {c t : Fin n} (hct : c ≠ t) {G : Mat1}
    (hG : ∀ b, G b (!b) = 0) (ψ : Vec n) :
    applyCNOT c t (applyOne G c ψ) = applyOne G c (applyCNOT c t ψ) := by
  funext x
  simp only [applyCNOT, applyOne_of_diag hG, bit_flipBit_of_ne hct]
  split_ifs <;> rfl

/-- A diagonal gate (`Z`, `S`, `S†`, `T`, `T†`) commutes with a CNOT on its
control, on any number of qubits. -/
theorem cnot_diag_control_comm {c t : Fin n} (hct : c ≠ t) {A : Gate1}
    (hA : ∀ b, A.mat b (!b) = 0) :
    [Instr.one A c, Instr.cnot c t] ≡ᵤ [Instr.cnot c t, Instr.one A c] :=
  fun ψ => applyCNOT_applyOne_control_comm hct hA ψ

/-! ### Moving a gate past a circuit that ignores its qubit -/

namespace Instr

/-- Whether an instruction acts on qubit `i`. -/
def touches (g : Instr n) (i : Fin n) : Prop :=
  match g with
  | one _ j => j = i
  | cnot c t => c = i ∨ t = i

instance (g : Instr n) (i : Fin n) : Decidable (g.touches i) :=
  match g with
  | one _ j => inferInstanceAs (Decidable (j = i))
  | cnot c t => inferInstanceAs (Decidable (c = i ∨ t = i))

@[simp] lemma touches_one (g : Gate1) (j i : Fin n) : (one g j).touches i ↔ j = i := Iff.rfl
@[simp] lemma touches_cnot (c t i : Fin n) : (cnot c t).touches i ↔ c = i ∨ t = i := Iff.rfl

end Instr

/-- A single-qubit gate commutes past every circuit that never touches its
qubit. -/
theorem denote_applyOne_comm_of_not_touches (c : Circuit n) (i : Fin n) (A : Mat1)
    (h : ∀ g ∈ c, ¬ g.touches i) (ψ : Vec n) :
    denote c (applyOne A i ψ) = applyOne A i (denote c ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih =>
    have hg := h g (List.mem_cons_self ..)
    have hc : ∀ g' ∈ c, ¬ g'.touches i := fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    simp only [denote_cons]
    rw [← ih hc]
    congr 1
    cases g with
    | one B j =>
      have hji : j ≠ i := hg
      exact applyOne_comm hji B.mat A ψ
    | cnot ct tt =>
      have hic : i ≠ ct := fun e => hg (Or.inl e.symm)
      have hit : i ≠ tt := fun e => hg (Or.inr e.symm)
      exact (applyOne_applyCNOT_comm hic hit A ψ).symm

/-! ### Layers -/

/-- A layer: the gate `g` on each qubit listed in `l`. -/
def layer (g : Gate1) (l : List (Fin n)) : Circuit n := l.map (Instr.one g)

@[simp] lemma layer_nil (g : Gate1) : layer g ([] : List (Fin n)) = [] := rfl

@[simp] lemma layer_cons (g : Gate1) (a : Fin n) (l : List (Fin n)) :
    layer g (a :: l) = Instr.one g a :: layer g l := rfl

lemma not_touches_layer_of_not_mem {g : Gate1} {l : List (Fin n)} {a : Fin n} (ha : a ∉ l) :
    ∀ g' ∈ layer g l, ¬ g'.touches a := by
  intro g' hg'
  simp only [layer, List.mem_map] at hg'
  obtain ⟨j, hj, rfl⟩ := hg'
  exact fun e => ha (e ▸ hj)

/-- A layer of an involutive gate on distinct qubits cancels against itself.
The proof moves each second copy of the gate back to its first copy using
`denote_applyOne_comm_of_not_touches`, fuses, and recurses. -/
theorem layer_layer_cancel {g : Gate1} (hg : g.mat * g.mat = 1) (l : List (Fin n))
    (hl : l.Nodup) : layer g l ++ layer g l ≡ᵤ [] := by
  induction l with
  | nil => exact Equivalent.refl _
  | cons a l ih =>
    intro ψ
    have hal : a ∉ l := (List.nodup_cons.1 hl).1
    have key := denote_applyOne_comm_of_not_touches (layer g l) a g.mat
      (not_touches_layer_of_not_mem hal)
    simp only [layer_cons, List.cons_append, denote_cons, denote_append, Instr.apply_one, key,
      applyOne_applyOne_same, hg, applyOne_one]
    simpa [denote_append] using ih (List.nodup_cons.1 hl).2 ψ

/-- A Hadamard on every qubit. -/
def hLayer (n : ℕ) : Circuit n := layer .H (List.finRange n)

/-- Two Hadamard layers cancel, for every `n`. -/
theorem hLayer_hLayer (n : ℕ) : hLayer n ++ hLayer n ≡ᵤ [] :=
  layer_layer_cancel Gate1.H_mul_H _ (List.nodup_finRange n)

/-! ### Inverse circuits

`inverse c` runs the inverse gates in reverse order. It undoes `c` whenever
every CNOT in `c` has distinct control and target (`applyCNOT c c` is a
projection, not an involution), which is the only proviso in
`denote_inverse_denote` and `denote_denote_inverse`. -/

namespace Instr

/-- The inverse instruction: the inverse gate on the same wire; a CNOT is
its own inverse. -/
def inverse : Instr n → Instr n
  | one g i => one g.inverse i
  | cnot c t => cnot c t

@[simp] lemma inverse_one (g : Gate1) (i : Fin n) : (one g i).inverse = one g.inverse i := rfl

@[simp] lemma inverse_cnot (c t : Fin n) : (cnot c t).inverse = cnot c t := rfl

/-- Inverting twice is the identity. -/
@[simp] lemma inverse_inverse (g : Instr n) : g.inverse.inverse = g := by
  cases g with
  | one g i => cases g <;> rfl
  | cnot c t => rfl

/-- The inverse instruction undoes the instruction; a CNOT needs distinct
wires. -/
lemma inverse_apply_apply (g : Instr n) (h : ∀ c t, g = cnot c t → c ≠ t) (ψ : Vec n) :
    g.inverse.apply (g.apply ψ) = ψ := by
  cases g with
  | one A i => simp [applyOne_applyOne_same, Gate1.inverse_mul, applyOne_one]
  | cnot c t => exact applyCNOT_applyCNOT_self (h c t rfl) ψ

end Instr

/-- The inverse circuit: the inverse instructions in reverse order. -/
def inverse (c : Circuit n) : Circuit n := (c.map Instr.inverse).reverse

@[simp] lemma inverse_nil : inverse ([] : Circuit n) = [] := rfl

@[simp] lemma inverse_cons (g : Instr n) (c : Circuit n) :
    inverse (g :: c) = inverse c ++ [g.inverse] := by
  simp [inverse]

/-- Inverting twice is the identity. -/
@[simp] lemma inverse_inverse (c : Circuit n) : inverse (inverse c) = c := by
  simp [inverse, List.map_reverse, List.map_map, Function.comp_def]

/-- A CNOT of the inverse circuit is a CNOT of the circuit. -/
lemma cnot_mem_of_mem_inverse {c : Circuit n} {a b : Fin n} (h : Instr.cnot a b ∈ inverse c) :
    Instr.cnot a b ∈ c := by
  simp only [inverse, List.mem_reverse, List.mem_map] at h
  obtain ⟨g, hg, hga⟩ := h
  cases g with
  | one _ _ => exact absurd hga (by simp)
  | cnot _ _ => exact hga ▸ hg

/-- The inverse circuit undoes the circuit, provided every CNOT has distinct
control and target. -/
theorem denote_inverse_denote (c : Circuit n) (h : ∀ a b, Instr.cnot a b ∈ c → a ≠ b)
    (ψ : Vec n) : denote (inverse c) (denote c ψ) = ψ := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih =>
    have hc : ∀ a b, Instr.cnot a b ∈ c → a ≠ b :=
      fun a b hm => h a b (List.mem_cons_of_mem _ hm)
    rw [inverse_cons, denote_cons, denote_append, ih hc, denote_cons, denote_nil]
    exact g.inverse_apply_apply (fun a b hg => h a b (hg ▸ List.mem_cons_self ..)) ψ

/-- The circuit undoes its inverse, under the same proviso. -/
theorem denote_denote_inverse (c : Circuit n) (h : ∀ a b, Instr.cnot a b ∈ c → a ≠ b)
    (ψ : Vec n) : denote c (denote (inverse c) ψ) = ψ := by
  have := denote_inverse_denote (inverse c) (fun a b hm => h a b (cnot_mem_of_mem_inverse hm)) ψ
  rwa [inverse_inverse] at this

end Quantum.Circuit
