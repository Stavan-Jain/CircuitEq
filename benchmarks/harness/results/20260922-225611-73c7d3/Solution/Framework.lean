import CircuitEq
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Quantum.Circuit.Harness
open Instr
variable {n : ℕ}
def rawMotif (a b t : Fin n) : Circuit n :=
 [H t, H t, CX b t, Tdg t, CX a t, T t, CX b t, Tdg t, CX a t,
  T b, T t, H t, CX a b, T a, Tdg b, CX a b, H t]
def diagMotif (a b t : Fin n) : Circuit n :=
 [CX b t, Tdg t, CX a t, T t, CX b t, Tdg t, CX a t,
  T b, T t, CX a b, T a, Tdg b, CX a b]
theorem motif_small : rawMotif (0 : Fin 3) 1 2 ≡ᵤ diagMotif 0 1 2 := by
 decide +kernel
theorem motif_sound (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
 rawMotif a b t ≡ᵤ diagMotif a b t := by
 simpa [rawMotif, diagMotif, rename, Instr.rename, wires₃] using
  motif_small.rename (wires₃ hab hat hbt)
theorem flatten_equiv {xs ys : List (Circuit n)}
 (h : List.Forall₂ Equivalent xs ys) : xs.flatten ≡ᵤ ys.flatten := by
 induction h with
 | nil => exact Equivalent.refl []
 | cons h hs ih => exact h.append ih
theorem motifs_sound (t : Fin n) (ps : List (Fin n × Fin n))
 (h : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) :
 (ps.flatMap fun p => rawMotif p.1 p.2 t) ≡ᵤ
 (ps.flatMap fun p => diagMotif p.1 p.2 t) := by
 induction ps with
 | nil => exact Equivalent.refl []
 | cons p ps ih =>
  exact (motif_sound _ _ _ (h p (by simp)).1 (h p (by simp)).2.1
   (h p (by simp)).2.2).append (ih (by intro p hp; exact h p (by simp [hp])))

def bodies (gs : List (Fin n × Circuit n)) : Circuit n := gs.flatMap Prod.snd
def heads (gs : List (Fin n × Circuit n)) : Circuit n := layer .H (gs.map Prod.fst)
def distributed (gs : List (Fin n × Circuit n)) : Circuit n :=
 gs.flatMap fun p => H p.1 :: p.2

def separateCheck : List (Fin n × Circuit n) → Bool
 | [] => true
 | (_, c) :: gs => masksDisjoint (support (heads gs)) (support c) && separateCheck gs

theorem blocks_disjoint (a b : Circuit n)
 (h : masksDisjoint (support a) (support b) = true) : a ++ b ≡ᵤ b ++ a := by
 apply blocks_comm
 intro g hg k hk
 apply Instr.CanCommute.sound
 apply Instr.CanCommute.of_no_shared_wire
 rintro i ⟨hi, hj⟩
 have ha : (support a).testBit i.val = true := by
  rw [support_testBit]; simpa using ⟨g, hg, hi⟩
 exact not_touches_of_disjoint (masksDisjoint_iff.mp h) ha k hk hj

theorem distribute_sound (gs : List (Fin n × Circuit n)) (h : separateCheck gs = true) :
 heads gs ++ bodies gs ≡ᵤ distributed gs := by
 induction gs with
 | nil => exact Equivalent.refl []
 | cons p gs ih =>
  have hh := Bool.and_eq_true_iff.mp h
  have hc := blocks_disjoint (heads gs) p.2 hh.1
  have hi := ih hh.2
  simpa [heads, bodies, distributed, layer, List.append_assoc] using
   ((hc.append (Equivalent.refl (bodies gs))).trans
    (by simpa [List.append_assoc] using (Equivalent.refl p.2).append hi)).cons (H p.1)
theorem with_head (r a b s : Circuit n) (t : Fin n)
 (h : r ++ a ≡ᵤ b ++ s)
 (hc : masksDisjoint (support r) (support [H t]) = true) :
 r ++ (H t :: a) ≡ᵤ (H t :: b) ++ s := by
 have hh := (blocks_disjoint r [H t] hc).append (Equivalent.refl a)
 calc
  _ ≡ᵤ [H t] ++ (r ++ a) := by simpa [List.append_assoc] using hh
  _ ≡ᵤ _ := by simpa using h.cons (H t)

theorem stitch {r s t a b c d : Circuit n}
 (h : r ++ a ≡ᵤ b ++ s) (k : s ++ c ≡ᵤ d ++ t) :
 r ++ (a ++ c) ≡ᵤ (b ++ d) ++ t := by
 have h1 := h.append (Equivalent.refl c)
 have h2 := (Equivalent.refl b).append k
 calc
  _ ≡ᵤ b ++ (s ++ c) := by simpa [List.append_assoc] using h1
  _ ≡ᵤ _ := by simpa [List.append_assoc] using h2
end Quantum.Circuit.Harness
