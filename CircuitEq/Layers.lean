/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Rewriting
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.SymmDiff

/-! # Hadamard layers and CNOT networks

Layer algebra and network conjugation work for arbitrary register sizes.
Swapping edge endpoints never reverses the order of the instructions.
-/

namespace Quantum.Circuit

open Instr
open scoped symmDiff
variable {n : ℕ}

/-- A CNOT network listed in time order, as control-target pairs. -/
def cnotNetwork (edges : List (Fin n × Fin n)) : Circuit n :=
  edges.map fun e => CX e.1 e.2

/-- Reverse each CNOT's direction, preserving instruction order. -/
def swapEndpoints (edges : List (Fin n × Fin n)) : List (Fin n × Fin n) :=
  edges.map Prod.swap

/-- A single CNOT passes through a layer containing both its wires. -/
theorem cnot_layer (wires : List (Fin n)) (hw : wires.Nodup)
    {c t : Fin n} (hct : c ≠ t) (hc : c ∈ wires) (ht : t ∈ wires) :
    [CX c t] ++ layer .H wires ≡ᵤ layer .H wires ++ [CX t c] := by
  let rest := (wires.erase c).erase t
  have hp : wires.Perm (c :: t :: rest) :=
    (List.perm_cons_erase hc).trans
      ((List.perm_cons_erase ((List.mem_erase_of_ne hct.symm).mpr ht)).cons c)
  have hn := hp.nodup hw
  have hrc : c ∉ rest := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hrt : t ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hm : [CX t c] ++ layer .H rest ≡ᵤ layer .H rest ++ [CX t c] := by
    apply gate_block_comm
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    exact Instr.CanCommute.sound (Or.inr (Or.inl
      ⟨fun h => hrt (h ▸ hi), fun h => hrc (h ▸ hi)⟩))
  calc
    _ ≡ᵤ [CX c t] ++ layer .H (c :: t :: rest) :=
      (Equivalent.refl _).append (layer_perm .H hp)
    _ ≡ᵤ [H c, H t] ++ [CX t c] ++ layer .H rest :=
      (cnot_hadamards_reverse hct).in_context [] (layer .H rest)
    _ ≡ᵤ layer .H (c :: t :: rest) ++ [CX t c] := by
      simpa [List.append_assoc] using hm.in_context [H c, H t] []
    _ ≡ᵤ layer .H wires ++ [CX t c] :=
      (layer_perm .H hp.symm).append (Equivalent.refl _)

/-- Move a Hadamard layer through a whole network on its wires. -/
theorem cnotNetwork_layer (edges : List (Fin n × Fin n)) (wires : List (Fin n))
    (hw : wires.Nodup) (he : ∀ e ∈ edges, e.1 ≠ e.2 ∧ e.1 ∈ wires ∧ e.2 ∈ wires) :
    cnotNetwork edges ++ layer .H wires ≡ᵤ
      layer .H wires ++ cnotNetwork (swapEndpoints edges) := by
  induction edges with
  | nil => simpa [cnotNetwork, swapEndpoints] using Equivalent.refl (layer .H wires)
  | cons e edges ih =>
    have h := he e (by simp)
    have ht := ih (fun x hx => he x (by simp [hx]))
    simpa [cnotNetwork, swapEndpoints, List.append_assoc] using
      (ht.cons (CX e.1 e.2)).trans
        ((cnot_layer wires hw h.1 h.2.1 h.2.2).in_context []
          (cnotNetwork (swapEndpoints edges)))

/-- Full-register Hadamards reverse every valid CNOT in a network. -/
theorem cnotNetwork_hLayer (edges : List (Fin n × Fin n))
    (he : ∀ e ∈ edges, e.1 ≠ e.2) :
    cnotNetwork edges ++ hLayer n ≡ᵤ hLayer n ++ cnotNetwork (swapEndpoints edges) :=
  cnotNetwork_layer edges _ (List.nodup_finRange n)
    (fun e h => ⟨he e h, List.mem_finRange _, List.mem_finRange _⟩)

/-- A Hadamard layer with its wires stored as a finite set in sorted order. -/
def hOn (s : Finset (Fin n)) : Circuit n := layer .H (s.sort (· ≤ ·))

/-- A duplicate-free list gives the same layer as its set of wires. -/
theorem layer_eq_hOn (wires : List (Fin n)) (hw : wires.Nodup) :
    layer .H wires ≡ᵤ hOn wires.toFinset := by
  apply layer_perm
  apply (List.perm_ext_iff_of_nodup hw (Finset.sort_nodup _ _)).mpr
  simp

/-- Extract any member of a set-indexed layer at its front. -/
theorem hOn_insert (a : Fin n) (s : Finset (Fin n)) (ha : a ∉ s) :
    hOn (insert a s) ≡ᵤ [H a] ++ hOn s := by
  change layer .H ((insert a s).sort (· ≤ ·)) ≡ᵤ layer .H (a :: s.sort (· ≤ ·))
  apply layer_perm .H
  apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
    (List.nodup_cons.mpr ⟨by simpa using ha, Finset.sort_nodup _ _⟩)).mpr
  simp

/-- A Hadamard toggles membership of its wire in a layer. -/
theorem hOn_toggle (a : Fin n) (s : Finset (Fin n)) :
    [H a] ++ hOn s ≡ᵤ hOn ({a} ∆ s) := by
  by_cases ha : a ∈ s
  · have hi := hOn_insert a (s.erase a) (by simp)
    rw [Finset.insert_erase ha] at hi
    have hd : ({a} : Finset (Fin n)) ∆ s = s.erase a := by
      ext x; by_cases hx : x = a <;> simp [Finset.mem_symmDiff, hx, ha]
    rw [hd]
    calc
      _ ≡ᵤ [H a] ++ ([H a] ++ hOn (s.erase a)) :=
        (Equivalent.refl _).append hi
      _ ≡ᵤ hOn (s.erase a) :=
        (cancel_of_mul_eq_one Gate1.H_mul_H a).in_context [] (hOn (s.erase a))
  · have hd : ({a} : Finset (Fin n)) ∆ s = insert a s := by
      ext x; by_cases hx : x = a <;> simp [Finset.mem_symmDiff, hx, ha]
    rw [hd]
    exact (hOn_insert a s ha).symm

/-- Combining two Hadamard layers cancels their common wires. -/
theorem hOn_symmDiff (s t : Finset (Fin n)) : hOn s ++ hOn t ≡ᵤ hOn (s ∆ t) := by
  induction s using Finset.induction_on with
  | empty => simpa [hOn, layer, symmDiff] using Equivalent.refl (hOn t)
  | @insert a s ha ih =>
    have hs : insert a s = ({a} : Finset (Fin n)) ∆ s := by
      ext x; by_cases hx : x = a <;> simp [Finset.mem_symmDiff, hx, ha]
    calc
      _ ≡ᵤ ([H a] ++ hOn s) ++ hOn t :=
        (hOn_insert a s ha).append (Equivalent.refl _)
      _ ≡ᵤ [H a] ++ hOn (s ∆ t) := by
        simpa [List.append_assoc] using ih.cons (H a)
      _ ≡ᵤ hOn (insert a s ∆ t) := by
        simpa [hs, symmDiff_assoc] using hOn_toggle a (s ∆ t)

/-- Full-register Hadamards are the set-indexed layer on all wires. -/
theorem hLayer_eq_hOn (n : ℕ) : hLayer n ≡ᵤ hOn (Finset.univ : Finset (Fin n)) := by
  simpa [hLayer] using layer_eq_hOn (List.finRange n) (List.nodup_finRange n)

/-- A seeded encoder followed by full Hadamards retains the complementary
seed layer and reverses every CNOT. -/
theorem hOn_cnotNetwork_hLayer (seed : Finset (Fin n)) (edges : List (Fin n × Fin n))
    (he : ∀ e ∈ edges, e.1 ≠ e.2) :
    hOn seed ++ cnotNetwork edges ++ hLayer n ≡ᵤ
      hOn (Finset.univ \ seed) ++ cnotNetwork (swapEndpoints edges) := by
  have hs : seed ∆ Finset.univ = Finset.univ \ seed := by
    ext x; simp [Finset.mem_symmDiff]
  calc
    _ ≡ᵤ (hOn seed ++ hLayer n) ++ cnotNetwork (swapEndpoints edges) := by
      simpa [List.append_assoc] using (cnotNetwork_hLayer edges he).in_context (hOn seed) []
    _ ≡ᵤ (hOn seed ++ hOn Finset.univ) ++ cnotNetwork (swapEndpoints edges) :=
      ((Equivalent.refl _).append (hLayer_eq_hOn n)).append (Equivalent.refl _)
    _ ≡ᵤ _ := by
      simpa [hs] using (hOn_symmDiff seed Finset.univ).append
        (Equivalent.refl (cnotNetwork (swapEndpoints edges)))

/-- The same, with the seed as a duplicate-free list: the surviving
Hadamards sit on the wires outside the seed, in register order. Both sides
reduce to explicit instruction lists for concrete `n`, so this is the form a
benchmark proof applies. -/
theorem layer_cnotNetwork_hLayer (seed : List (Fin n)) (hs : seed.Nodup)
    (edges : List (Fin n × Fin n)) (he : ∀ e ∈ edges, e.1 ≠ e.2) :
    layer .H seed ++ cnotNetwork edges ++ hLayer n ≡ᵤ
      layer .H ((List.finRange n).diff seed) ++ cnotNetwork (swapEndpoints edges) := by
  have hd : ((List.finRange n).diff seed).toFinset = Finset.univ \ seed.toFinset := by
    ext x
    simp [(List.nodup_finRange n).mem_diff_iff]
  calc
    _ ≡ᵤ hOn seed.toFinset ++ cnotNetwork edges ++ hLayer n :=
      ((layer_eq_hOn seed hs).append (Equivalent.refl _)).append (Equivalent.refl _)
    _ ≡ᵤ hOn (Finset.univ \ seed.toFinset) ++ cnotNetwork (swapEndpoints edges) :=
      hOn_cnotNetwork_hLayer seed.toFinset edges he
    _ ≡ᵤ _ := by
      rw [← hd]
      exact (layer_eq_hOn _ (List.nodup_finRange n).diff).symm.append (Equivalent.refl _)

/-- A CNOT network between disjoint control and target sets can be permuted. -/
theorem cnotNetwork_perm {edges other : List (Fin n × Fin n)}
    (controls targets : Finset (Fin n)) (hd : Disjoint controls targets)
    (he : ∀ e ∈ edges, e.1 ∈ controls ∧ e.2 ∈ targets) (hp : edges.Perm other) :
    cnotNetwork edges ≡ᵤ cnotNetwork other := by
  apply perm_equivalent (hp.map _)
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  apply cnot_cnot_comm
  · intro h
    exact Finset.disjoint_left.mp hd (he a ha).1 (h ▸ (he b hb).2)
  · intro h
    exact Finset.disjoint_left.mp hd (he b hb).1 (h ▸ (he a ha).2)

end Quantum.Circuit
