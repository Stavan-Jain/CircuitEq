/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Structural

/-!
# Wire supports as bitmasks

The wires an instruction or a circuit touches, as a `Nat` whose bit `i` is
set iff wire `i` is touched. Every checker and the certificate language use
this one encoding, so that "do these share a wire" is a single `Nat.land`,
which the kernel evaluates with GMP, and the support of a block is a fold
of `Nat.lor`. Do not introduce a second encoding of wire sets.

`Instr.support_testBit` and `support_testBit` tie the masks to
`Instr.touches`; `not_touches_of_disjoint` turns a disjoint mask into the
hypothesis of `denote_applyOne_comm_of_not_touches`, and
`CircuitEq.Rewriting` turns it into `Instr.CanCommute`.
-/

namespace Quantum.Circuit

variable {n : ℕ}

/-- The wires an instruction touches, as a bitmask. -/
def Instr.support : Instr n → ℕ
  | .one _ i => 2 ^ i.val
  | .cnot c t => 2 ^ c.val ||| 2 ^ t.val

@[simp] lemma Instr.support_one (g : Gate1) (i : Fin n) :
    (Instr.one g i).support = 2 ^ i.val := rfl

@[simp] lemma Instr.support_cnot (c t : Fin n) :
    (Instr.cnot c t).support = 2 ^ c.val ||| 2 ^ t.val := rfl

/-- Bit `i` of an instruction's support is set iff it touches wire `i`. -/
lemma Instr.support_testBit (g : Instr n) (i : Fin n) :
    g.support.testBit i.val = decide (g.touches i) := by
  cases g with
  | one _ j => simp only [Instr.support_one, Instr.touches_one, Nat.testBit_two_pow, Fin.ext_iff]
  | cnot c t =>
    simp only [Instr.support_cnot, Instr.touches_cnot, Nat.testBit_or, Nat.testBit_two_pow,
      Fin.ext_iff, Bool.decide_or]

/-- The wires a circuit touches, as a bitmask. -/
def support (c : Circuit n) : ℕ := c.foldr (fun g m => g.support ||| m) 0

@[simp] lemma support_nil : support ([] : Circuit n) = 0 := rfl

@[simp] lemma support_cons (g : Instr n) (c : Circuit n) :
    support (g :: c) = g.support ||| support c := rfl

@[simp] lemma support_append (c₁ c₂ : Circuit n) :
    support (c₁ ++ c₂) = support c₁ ||| support c₂ := by
  induction c₁ with
  | nil => simp
  | cons g c ih => simp [ih, Nat.lor_assoc]

/-- Bit `i` of a circuit's support is set iff some instruction touches
wire `i`. -/
lemma support_testBit (c : Circuit n) (i : Fin n) :
    (support c).testBit i.val = decide (∃ g ∈ c, g.touches i) := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [support_cons, Nat.testBit_or, Instr.support_testBit, ih, List.exists_mem_cons_iff,
      Bool.decide_or]

/-- Whether two masks share no set bit; the kernel-facing test. -/
def masksDisjoint (a b : ℕ) : Bool := a &&& b == 0

lemma masksDisjoint_iff {a b : ℕ} : masksDisjoint a b = true ↔ a &&& b = 0 := by
  simp [masksDisjoint]

/-- A mask disjoint from a circuit's support touches none of its wires. -/
lemma not_touches_of_disjoint {m : ℕ} {c : Circuit n} (h : m &&& support c = 0)
    {i : Fin n} (hi : m.testBit i.val = true) : ∀ g ∈ c, ¬ g.touches i := by
  intro g hg ht
  have h1 : (m &&& support c).testBit i.val = true := by
    rw [Nat.testBit_land, hi, support_testBit]
    simpa using ⟨g, hg, ht⟩
  rw [h, Nat.zero_testBit] at h1
  exact Bool.false_ne_true h1

/-- Instructions with disjoint supports share no wire. -/
lemma Instr.not_touches_both_of_disjoint {a b : Instr n} (h : a.support &&& b.support = 0)
    (i : Fin n) : ¬ (a.touches i ∧ b.touches i) := by
  rintro ⟨ha, hb⟩
  have h1 : (a.support &&& b.support).testBit i.val = true := by
    rw [Nat.testBit_land, Instr.support_testBit, Instr.support_testBit]
    simp [ha, hb]
  rw [h, Nat.zero_testBit] at h1
  exact Bool.false_ne_true h1

/-- A single-qubit gate commutes past a circuit whose support avoids its
wire: the mask form of `denote_applyOne_comm_of_not_touches`. -/
theorem denote_applyOne_comm_of_disjoint (c : Circuit n) (i : Fin n) (A : Mat1)
    (h : 2 ^ i.val &&& support c = 0) (ψ : Vec n) :
    denote c (applyOne A i ψ) = applyOne A i (denote c ψ) :=
  denote_applyOne_comm_of_not_touches c i A
    (not_touches_of_disjoint h Nat.testBit_two_pow_self) ψ

end Quantum.Circuit
