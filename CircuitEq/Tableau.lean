/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Structural
import CircuitEq.Checker
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The Clifford tableau checker

A certified decision procedure for the Clifford fragment (`H`, `X`, `Y`,
`Z`, `S`, `S†` and `CX`; `T` and `T†` are outside it). `tableauChecker n :
ScalarChecker n` decides `a ≡ₛ b` by computing the *tableau* of each
circuit, the images of the `2n` Pauli generators `X_j`, `Z_j` under
conjugation by the circuit, and comparing the two lists. A Clifford unitary
is determined by that conjugation action up to a global scalar, which is why
the certified relation is `≡ₛ` and not `≡ᵤ`: the tableau never sees the
scalar, and showing it is a power of `ω` is number theory in `ℤ[ω]` that this
library does not do. Memory is `2n` strings of `2n` bits, a gate costs `O(n)`
bit operations, and no object of size `2 ^ n` is ever built, so circuits on
hundreds of qubits are within reach of the kernel.

## Pauli strings

`Pauli` is an x-mask, a z-mask (both `Nat` bitmasks, bit `j` for wire `j`,
the encoding of `CircuitEq.Support`) and a phase `p : Fin 4`, denoting
`i ^ p · Z^z · X^x`: `Z` factors stand to the left of `X` factors, so on a
single wire `⟨1, 1, 0⟩` is `Z X = i Y`. As an operator on `Vec n`,

```
(Pauli.op ⟨x, z, p⟩ ψ) w = i ^ p · (−1)^{⟨z, w⟩} · ψ (w ⊕ x)
```

with `sign z w = (−1)^{⟨z, w⟩}` a product over the wires (a `Finset.prod`,
which is fine because the kernel never evaluates `op`, only the update).

## Update rules

Conjugation by a Clifford gate `U` sends the string `P` to `U P U†`, again
a Pauli string, and the `Z`-left convention makes every rule a couple of
bit operations with no reordering except in `H`:

- `H_j`: swap `x_j` and `z_j`; phase `+2` when both were set (`Z X ↦ X Z =
  −Z X`).
- `S_j`: `X ↦ Y = −i Z X`, so `z_j ^= x_j` and phase `+3` when `x_j` is set;
  `S†_j` likewise with phase `+1`.
- `X_j`, `Y_j`, `Z_j`: phase `+2` when the string anticommutes with the gate.
- `CX c t`: `x_t ^= x_c`, `z_c ^= z_t`, no phase: all `Z` factors stay left
  of all `X` factors.

Each rule is proved sound pointwise (`conjH_sound`, …, `conjCX_sound`):
`U (P.op ψ) = (conj P).op (U ψ)` for every `ψ`, by the `bit`/`flipBit`
lemmas of `CircuitEq.Bits`, the `sign` and `xorMask` lemmas below, and a
case split on the three relevant bits.

## Soundness

If `tableau a = tableau b = some T`, then for every generator `P` both
circuits satisfy `denote c (P.op ψ) = Q.op (denote c ψ)` with the same `Q`
(`conj_sound`). With the inverse circuit of `CircuitEq.Structural`, the
operator `W ψ := denote (inverse b) (denote a ψ)` therefore commutes with
every generator, and an operator commuting with all `Z_j` is diagonal in the
computational basis while commuting with all `X_j` makes the diagonal
constant (`eq_smul_of_comm_generators`), so `W = λ • id` by linearity and
`denote a ψ = λ • denote b ψ`. The same argument with the roles swapped
produces `λ⁻¹`, so `λ` is a unit.

## What the kernel runs

`tableauCheck a b` is `Bool` code over `Nat` bit operations, `Fin 4`
addition and list recursion: `conj` folds a gate update over the circuit
for each of the `2n` generators, and the two `Option (List Pauli)` results
are compared by the derived `DecidableEq`. Nothing touches `Zeta8`, so
`decide +kernel` on the check costs `O(n · gates)` machine-word operations
and the seven-qubit benchmarks below decide in milliseconds.
-/

namespace Quantum.Circuit

open Zeta8

variable {n : ℕ}

/-! ### Pauli strings -/

/-- A Pauli string with a phase: `⟨x, z, p⟩` denotes `i ^ p · Z^z · X^x`,
where `X^x` is `X` on every wire whose bit is set in the mask `x`, `Z^z`
likewise, and `Z` factors stand to the left of `X` factors. -/
structure Pauli where
  /-- The wires carrying an `X` factor, as a bitmask. -/
  x : ℕ
  /-- The wires carrying a `Z` factor, as a bitmask. -/
  z : ℕ
  /-- The phase, as the exponent of `i`. -/
  phase : Fin 4
  deriving DecidableEq, Repr

/-- `i ^ p`, the scalar of a phase. -/
def phaseVal (p : Fin 4) : Zeta8 := I ^ p.val

/-- Phases add modulo four. -/
lemma phaseVal_add (p q : Fin 4) : phaseVal (p + q) = phaseVal p * phaseVal q := by
  revert p q; decide +kernel

@[simp] lemma phaseVal_zero : phaseVal 0 = 1 := by decide +kernel
lemma phaseVal_one : phaseVal 1 = I := by decide +kernel
lemma phaseVal_two : phaseVal 2 = -1 := by decide +kernel
lemma phaseVal_three : phaseVal 3 = -I := by decide +kernel

/-- `(−1)^{⟨z, w⟩}`: the sign `Z^z` gives the basis state `|w⟩`, as a
product over the wires. -/
def sign (z : ℕ) (w : Fin (2 ^ n)) : Zeta8 :=
  ∏ j : Fin n, if z.testBit j.val && bit j w then -1 else 1

@[simp] lemma sign_zero (w : Fin (2 ^ n)) : sign 0 w = 1 := by
  simp [sign]

/-- The sign is multiplicative in the mask. -/
lemma sign_xor (z z' : ℕ) (w : Fin (2 ^ n)) : sign (z ^^^ z') w = sign z w * sign z' w := by
  unfold sign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.testBit_xor]
  cases z.testBit j.val <;> cases z'.testBit j.val <;> cases bit j w <;> simp

/-- The sign of a single `Z_j`. -/
lemma sign_two_pow (j : Fin n) (w : Fin (2 ^ n)) :
    sign (2 ^ j.val) w = if bit j w then -1 else 1 := by
  unfold sign
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    have : j.val ≠ i.val := fun h => hij (Fin.ext h).symm
    simp [Nat.testBit_two_pow_of_ne this]
  · simp

/-- Flipping bit `j` of the basis index changes the sign by `z_j`. -/
lemma sign_flipBit (z : ℕ) (j : Fin n) (w : Fin (2 ^ n)) :
    sign z (flipBit j w) = (if z.testBit j.val then -1 else 1) * sign z w := by
  unfold sign
  have hfactor : ∀ i : Fin n,
      (if z.testBit i.val && bit i (flipBit j w) then (-1 : Zeta8) else 1) =
        (if i = j then (if z.testBit j.val then -1 else 1) else 1) *
          (if z.testBit i.val && bit i w then -1 else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [bit_flipBit_self, if_true]
      cases z.testBit i.val <;> cases bit i w <;> simp
    · simp [hij, bit_flipBit_of_ne hij]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j]
  simp

/-- `w ⊕ x`: the basis index with the wires of the mask `x` flipped (bits of
`x` beyond `n` are ignored). -/
def xorMask (x : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨(w.val ^^^ x) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

@[simp] lemma val_xorMask (x : ℕ) (w : Fin (2 ^ n)) :
    (xorMask x w).val = (w.val ^^^ x) % 2 ^ n := rfl

lemma testBit_xorMask (x : ℕ) (w : Fin (2 ^ n)) (i : ℕ) :
    (xorMask x w).val.testBit i = (decide (i < n) && (w.val.testBit i ^^ x.testBit i)) := by
  simp [Nat.testBit_mod_two_pow, Nat.testBit_xor]

@[simp] lemma xorMask_zero (w : Fin (2 ^ n)) : xorMask 0 w = w := by
  ext
  simp [Nat.mod_eq_of_lt w.isLt]

@[simp] lemma bit_xorMask (x : ℕ) (j : Fin n) (w : Fin (2 ^ n)) :
    bit j (xorMask x w) = (bit j w ^^ x.testBit j.val) := by
  simp [bit, j.isLt]

/-- Adding a wire to the mask flips that bit of the result. -/
lemma xorMask_xor_two_pow (x : ℕ) (j : Fin n) (w : Fin (2 ^ n)) :
    xorMask (x ^^^ 2 ^ j.val) w = flipBit j (xorMask x w) := by
  ext
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [val_xorMask, val_flipBit, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    Nat.testBit_two_pow]
  by_cases hi : i < n
  · simp only [hi, decide_true, Bool.true_and]
    cases w.val.testBit i <;> cases x.testBit i <;> cases decide (j.val = i) <;> simp
  · have hji : j.val ≠ i := fun h => hi (h ▸ j.isLt)
    simp [hi, hji]

/-- Flipping a bit of the index commutes with the mask. -/
lemma xorMask_flipBit (x : ℕ) (j : Fin n) (w : Fin (2 ^ n)) :
    xorMask x (flipBit j w) = flipBit j (xorMask x w) := by
  rw [← xorMask_xor_two_pow]
  ext
  simp only [val_xorMask, val_flipBit]
  rw [Nat.xor_assoc, Nat.xor_comm (2 ^ j.val) x]

/-- A single wire as a mask is a bit flip. -/
lemma xorMask_two_pow (j : Fin n) (w : Fin (2 ^ n)) : xorMask (2 ^ j.val) w = flipBit j w := by
  simpa using xorMask_xor_two_pow 0 j w

/-- The operator a Pauli string denotes: `i ^ p · Z^z · X^x`, pointwise. -/
def Pauli.op (P : Pauli) (ψ : Vec n) : Vec n :=
  fun w => phaseVal P.phase * sign P.z w * ψ (xorMask P.x w)

/-! ### The update rules -/

namespace Pauli

/-- Conjugation by `H_j`: swap `x_j` and `z_j`, with the sign flipped when
both were set. -/
def conjH (j : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x ^^^ (if (P.x.testBit j ^^ P.z.testBit j) then 2 ^ j else 0),
    P.z ^^^ (if (P.x.testBit j ^^ P.z.testBit j) then 2 ^ j else 0),
    P.phase + (if P.x.testBit j && P.z.testBit j then 2 else 0)⟩

/-- Conjugation by `S_j`: `X ↦ Y = −i Z X`. -/
def conjS (j : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x, P.z ^^^ (if P.x.testBit j then 2 ^ j else 0), P.phase + (if P.x.testBit j then 3 else 0)⟩

/-- Conjugation by `S†_j`: `X ↦ −Y = i Z X`. -/
def conjSdg (j : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x, P.z ^^^ (if P.x.testBit j then 2 ^ j else 0), P.phase + (if P.x.testBit j then 1 else 0)⟩

/-- Conjugation by `X_j` negates a `Z` factor on wire `j`. -/
def conjX (j : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x, P.z, P.phase + (if P.z.testBit j then 2 else 0)⟩

/-- Conjugation by `Z_j` negates an `X` factor on wire `j`. -/
def conjZ (j : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x, P.z, P.phase + (if P.x.testBit j then 2 else 0)⟩

/-- Conjugation by `Y_j` negates a lone `X` or `Z` factor on wire `j`. -/
def conjY (j : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x, P.z, P.phase + (if (P.x.testBit j ^^ P.z.testBit j) then 2 else 0)⟩

/-- Conjugation by `CX c t`: `X_c ↦ X_c X_t` and `Z_t ↦ Z_c Z_t`. -/
def conjCX (c t : ℕ) (P : Pauli) : Pauli :=
  ⟨P.x ^^^ (if P.x.testBit c then 2 ^ t else 0),
    P.z ^^^ (if P.z.testBit t then 2 ^ c else 0), P.phase⟩

/-- The `H` rule is sound. -/
theorem conjH_sound (j : Fin n) (P : Pauli) (ψ : Vec n) :
    applyOne Gate1.H.mat j (P.op ψ) = (P.conjH j.val).op (applyOne Gate1.H.mat j ψ) := by
  funext w
  simp only [applyOne, Pauli.op, conjH, Gate1.mat, Matrix.of_apply]
  cases hx : P.x.testBit j.val <;> cases hz : P.z.testBit j.val <;> cases hb : bit j w <;>
    simp [hx, hz, hb, sign_xor, sign_two_pow, sign_flipBit, xorMask_xor_two_pow, xorMask_flipBit,
      phaseVal_add, phaseVal_two] <;> ring

/-- The `S` rule is sound. -/
theorem conjS_sound (j : Fin n) (P : Pauli) (ψ : Vec n) :
    applyOne Gate1.S.mat j (P.op ψ) = (P.conjS j.val).op (applyOne Gate1.S.mat j ψ) := by
  funext w
  simp only [applyOne, Pauli.op, conjS, Gate1.mat, Matrix.of_apply]
  cases hx : P.x.testBit j.val <;> cases hb : bit j w <;>
    simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true,
      one_mul, mul_one, neg_mul, mul_neg, neg_neg, neg_zero, zero_mul, add_zero, ite_mul, mul_ite,
      ite_self, Fin.isValue, Fin.add_zero, Nat.xor_zero, bne_self_eq_false, Bool.bne_false,
      Bool.bne_true, sign_flipBit, sign_xor, sign_two_pow, xorMask_flipBit, bit_xorMask,
      phaseVal_add, phaseVal_three, hx, hb] <;>
    first
    | ring1
    | linear_combination (phaseVal P.phase * sign P.z w * ψ (xorMask P.x w)) * Zeta8.I_mul_I

/-- The `S†` rule is sound. -/
theorem conjSdg_sound (j : Fin n) (P : Pauli) (ψ : Vec n) :
    applyOne Gate1.Sdg.mat j (P.op ψ) = (P.conjSdg j.val).op (applyOne Gate1.Sdg.mat j ψ) := by
  funext w
  simp only [applyOne, Pauli.op, conjSdg, Gate1.mat, Matrix.of_apply]
  cases hx : P.x.testBit j.val <;> cases hb : bit j w <;>
    simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true,
      one_mul, mul_one, neg_mul, mul_neg, neg_zero, neg_inj, zero_mul, add_zero, ite_mul,
      mul_ite, ite_self, Fin.isValue, Fin.add_zero, Nat.xor_zero, bne_self_eq_false,
      Bool.bne_false, Bool.bne_true, sign_flipBit, sign_xor, sign_two_pow, xorMask_flipBit,
      bit_xorMask, phaseVal_add, phaseVal_one, hx, hb] <;>
    first
    | ring1
    | linear_combination (phaseVal P.phase * sign P.z w * ψ (xorMask P.x w)) * Zeta8.I_mul_I

/-- The `X` rule is sound. -/
theorem conjX_sound (j : Fin n) (P : Pauli) (ψ : Vec n) :
    applyOne Gate1.X.mat j (P.op ψ) = (P.conjX j.val).op (applyOne Gate1.X.mat j ψ) := by
  funext w
  simp only [applyOne, Pauli.op, conjX, Gate1.mat, Matrix.of_apply]
  cases hx : P.x.testBit j.val <;> cases hz : P.z.testBit j.val <;> cases hb : bit j w <;>
    simp [hx, hz, hb, sign_flipBit, xorMask_flipBit, phaseVal_add, phaseVal_two]

/-- The `Z` rule is sound. -/
theorem conjZ_sound (j : Fin n) (P : Pauli) (ψ : Vec n) :
    applyOne Gate1.Z.mat j (P.op ψ) = (P.conjZ j.val).op (applyOne Gate1.Z.mat j ψ) := by
  funext w
  simp only [applyOne, Pauli.op, conjZ, Gate1.mat, Matrix.of_apply]
  cases hx : P.x.testBit j.val <;> cases hb : bit j w <;>
    simp [hx, hb, sign_flipBit, xorMask_flipBit, phaseVal_add, phaseVal_two]

/-- The `Y` rule is sound. -/
theorem conjY_sound (j : Fin n) (P : Pauli) (ψ : Vec n) :
    applyOne Gate1.Y.mat j (P.op ψ) = (P.conjY j.val).op (applyOne Gate1.Y.mat j ψ) := by
  funext w
  simp only [applyOne, Pauli.op, conjY, Gate1.mat, Matrix.of_apply]
  cases hx : P.x.testBit j.val <;> cases hz : P.z.testBit j.val <;> cases hb : bit j w <;>
    simp [hx, hz, hb, sign_flipBit, xorMask_flipBit, phaseVal_add, phaseVal_two] <;> ring

/-- The `CX` rule is sound, for distinct control and target. -/
theorem conjCX_sound {c t : Fin n} (hct : c ≠ t) (P : Pauli) (ψ : Vec n) :
    applyCNOT c t (P.op ψ) = (P.conjCX c.val t.val).op (applyCNOT c t ψ) := by
  funext w
  simp only [applyCNOT, Pauli.op, conjCX]
  cases hxc : P.x.testBit c.val <;> cases hzt : P.z.testBit t.val <;> cases hwc : bit c w <;>
    simp [hxc, hzt, hwc, sign_xor, sign_two_pow, sign_flipBit, xorMask_xor_two_pow,
      xorMask_flipBit, bit_flipBit_of_ne hct]

end Pauli

/-- Conjugate a Pauli string by a single-qubit gate on wire `j`; `none` for
`T` and `T†`, which leave the Clifford fragment. -/
def Gate1.conj (g : Gate1) (j : ℕ) (P : Pauli) : Option Pauli :=
  match g with
  | .H => some (P.conjH j)
  | .S => some (P.conjS j)
  | .Sdg => some (P.conjSdg j)
  | .X => some (P.conjX j)
  | .Y => some (P.conjY j)
  | .Z => some (P.conjZ j)
  | .T | .Tdg => none

/-- Conjugate a Pauli string by one instruction; `none` outside the Clifford
fragment and for a CNOT whose control is its target. -/
def Instr.conj : Instr n → Pauli → Option Pauli
  | .one g i, P => g.conj i.val P
  | .cnot c t, P => if c = t then none else some (P.conjCX c.val t.val)

/-- One instruction's update is sound. -/
theorem Instr.conj_sound {g : Instr n} {P Q : Pauli} (h : g.conj P = some Q) (ψ : Vec n) :
    g.apply (P.op ψ) = Q.op (g.apply ψ) := by
  cases g with
  | one A i =>
    simp only [Instr.apply_one]
    cases A <;> simp only [Instr.conj, Gate1.conj, Option.some.injEq, reduceCtorEq] at h <;>
      subst h
    · exact Pauli.conjH_sound i P ψ
    · exact Pauli.conjX_sound i P ψ
    · exact Pauli.conjY_sound i P ψ
    · exact Pauli.conjZ_sound i P ψ
    · exact Pauli.conjS_sound i P ψ
    · exact Pauli.conjSdg_sound i P ψ
  | cnot c t =>
    by_cases hct : c = t
    · simp [Instr.conj, hct] at h
    · simp only [Instr.conj, hct, if_false, Option.some.injEq] at h
      subst h
      exact Pauli.conjCX_sound hct P ψ

/-! ### The tableau -/

/-- Conjugate a Pauli string by a whole circuit, gate by gate; `none` if any
gate is outside the fragment. -/
def conj : Circuit n → Pauli → Option Pauli
  | [], P => some P
  | g :: c, P =>
    match g.conj P with
    | none => none
    | some P' => conj c P'

/-- A circuit's update is sound: `denote c ∘ P.op = Q.op ∘ denote c`. -/
theorem conj_sound {c : Circuit n} {P Q : Pauli} (h : conj c P = some Q) (ψ : Vec n) :
    denote c (P.op ψ) = Q.op (denote c ψ) := by
  induction c generalizing P ψ with
  | nil =>
    simp only [conj, Option.some.injEq] at h
    subst h
    rfl
  | cons g c ih =>
    simp only [conj] at h
    split at h
    · exact absurd h (by simp)
    · rename_i P' hg
      simp only [denote_cons, g.conj_sound hg ψ]
      exact ih h _

/-- A circuit with a tableau has no CNOT whose control is its target. -/
theorem conj_proper {c : Circuit n} {P Q : Pauli} (h : conj c P = some Q) :
    ∀ a b, Instr.cnot a b ∈ c → a ≠ b := by
  induction c generalizing P with
  | nil => simp
  | cons g c ih =>
    intro a b hm
    simp only [conj] at h
    split at h
    · exact absurd h (by simp)
    · rename_i P' hg
      rcases List.mem_cons.1 hm with rfl | hm
      · intro hab
        simp [Instr.conj, hab] at hg
      · exact ih h a b hm

/-- The generator `X_j`. -/
def Pauli.xGen (j : Fin n) : Pauli := ⟨2 ^ j.val, 0, 0⟩

/-- The generator `Z_j`. -/
def Pauli.zGen (j : Fin n) : Pauli := ⟨0, 2 ^ j.val, 0⟩

/-- The `2n` generators of the Pauli group: `X_0, …, X_{n-1}, Z_0, …,
Z_{n-1}`. -/
def generators (n : ℕ) : List Pauli :=
  (List.finRange n).map Pauli.xGen ++ (List.finRange n).map Pauli.zGen

lemma xGen_mem_generators (j : Fin n) : Pauli.xGen j ∈ generators n := by
  simp [generators]

lemma zGen_mem_generators (j : Fin n) : Pauli.zGen j ∈ generators n := by
  simp [generators]

/-- Map a partial function over a list, failing if it fails anywhere. -/
def mapOpt {α β : Type*} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: l =>
    match f a, mapOpt f l with
    | some b, some r => some (b :: r)
    | _, _ => none

/-- Two partial functions with the same successful `mapOpt` agree, and
succeed, on every element. -/
lemma mapOpt_eq_some {α β : Type*} {f g : α → Option β} {l : List α} {r : List β}
    (hf : mapOpt f l = some r) (hg : mapOpt g l = some r) :
    ∀ a ∈ l, ∃ b, f a = some b ∧ g a = some b := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
    intro a' ha'
    simp only [mapOpt] at hf hg
    cases hfa : f a <;> cases hfl : mapOpt f l <;> simp only [hfa, hfl, reduceCtorEq] at hf
    cases hga : g a <;> cases hgl : mapOpt g l <;> simp only [hga, hgl, reduceCtorEq] at hg
    rename_i b r' b' r''
    simp only [Option.some.injEq] at hf hg
    subst hf
    obtain ⟨rfl, rfl⟩ := List.cons.inj hg
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact ⟨_, hfa, hga⟩
    · exact ih hfl hgl a' ha'

/-- The tableau of a circuit: the images of the `2n` generators under
conjugation by it, or `none` if the circuit leaves the Clifford fragment. -/
def tableau (c : Circuit n) : Option (List Pauli) := mapOpt (conj c) (generators n)

/-- The decision: both tableaux exist and are equal. -/
def tableauCheck (a b : Circuit n) : Bool :=
  match tableau a, tableau b with
  | some ta, some tb => decide (ta = tb)
  | _, _ => false

/-- A circuit with a tableau has no CNOT whose control is its target. -/
theorem tableau_proper {b : Circuit n} {T : List Pauli} (hb : tableau b = some T) :
    ∀ c t, Instr.cnot c t ∈ b → c ≠ t := by
  intro c t hm
  obtain ⟨Q, hQ, -⟩ := mapOpt_eq_some hb hb _ (xGen_mem_generators ⟨0, c.pos⟩)
  exact conj_proper hQ c t hm

/-! ### The commutant of the Pauli group is the scalars -/

/-- `Z_j` acts on `|w⟩` by the sign of bit `j`. -/
lemma zGen_op (j : Fin n) (ψ : Vec n) (w : Fin (2 ^ n)) :
    (Pauli.zGen j).op ψ w = (if bit j w then -1 else 1) * ψ w := by
  simp [Pauli.op, Pauli.zGen, sign_two_pow]

/-- `X_j` flips bit `j`. -/
lemma xGen_op (j : Fin n) (ψ : Vec n) (w : Fin (2 ^ n)) :
    (Pauli.xGen j).op ψ w = ψ (flipBit j w) := by
  simp [Pauli.op, Pauli.xGen, xorMask_two_pow]

/-- Distinct basis indices differ in some bit. -/
lemma exists_bit_ne {w y : Fin (2 ^ n)} (h : w ≠ y) : ∃ j : Fin n, bit j w ≠ bit j y := by
  by_contra hc
  apply h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · by_contra hne
    exact hc ⟨⟨i, hi⟩, hne⟩
  · have hn : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.1 hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt hn),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt hn)]

/-- A function on basis indices invariant under every bit flip is constant:
clear the set bits one at a time. -/
lemma eq_zero_of_flipBit_invariant {α : Type*} (f : Fin (2 ^ n) → α)
    (hf : ∀ j y, f (flipBit j y) = f y) (y : Fin (2 ^ n)) : f y = f ⟨0, Nat.two_pow_pos n⟩ := by
  obtain ⟨v, hv⟩ := y
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases h0 : v = 0
    · subst h0; rfl
    · obtain ⟨i, hi, -⟩ := Nat.exists_most_significant_bit h0
      have hin : i < n := by
        by_contra hni
        have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.1 hni)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv hle)] at hi
        exact Bool.false_ne_true hi
      have hlt : v ^^^ 2 ^ i < v :=
        Nat.lt_of_testBit i (by simp [Nat.testBit_xor, hi]) hi fun k hk => by
          simp [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (ne_of_lt hk)]
      have hv' : v ^^^ 2 ^ i < 2 ^ n := lt_trans hlt hv
      have hflip : flipBit ⟨i, hin⟩ ⟨v ^^^ 2 ^ i, hv'⟩ = ⟨v, hv⟩ := by
        ext
        simp
      rw [← hflip, hf]
      exact ih _ hlt hv'

/-- No two-torsion in `Zeta8`: `v + v = 0` forces `v = 0`. -/
lemma zeta8_eq_zero_of_add_self {v : Zeta8} (h : v + v = 0) : v = 0 := by
  rw [Zeta8.ext_iff] at h ⊢
  simp only [Zeta8.add_a, Zeta8.add_b, Zeta8.add_c, Zeta8.add_d, Zeta8.zero_a, Zeta8.zero_b,
    Zeta8.zero_c, Zeta8.zero_d] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A flip sends `v` to `y` iff it sends `y` to `v`. -/
lemma flipBit_eq_iff (j : Fin n) (v y : Fin (2 ^ n)) : flipBit j v = y ↔ v = flipBit j y :=
  ⟨fun h => by rw [← h, flipBit_flipBit_self], fun h => by rw [h, flipBit_flipBit_self]⟩

/-- A linear operator commuting with every `X_j` and `Z_j` is a scalar: the
`Z_j` make it diagonal in the computational basis, the `X_j` make the
diagonal constant. -/
theorem eq_smul_of_comm_generators (W : Vec n →ₗ[Zeta8] Vec n)
    (hX : ∀ (j : Fin n) ψ, W ((Pauli.xGen j).op ψ) = (Pauli.xGen j).op (W ψ))
    (hZ : ∀ (j : Fin n) ψ, W ((Pauli.zGen j).op ψ) = (Pauli.zGen j).op (W ψ)) :
    ∃ a : Zeta8, ∀ ψ, W ψ = a • ψ := by
  set lam : Fin (2 ^ n) → Zeta8 := fun y => W (basis y) y with hlam
  have hdiag : ∀ y, W (basis y) = lam y • basis y := by
    intro y
    funext w
    by_cases hwy : w = y
    · subst hwy
      simp [basis, hlam]
    · obtain ⟨j, hj⟩ := exists_bit_ne hwy
      have h2 : (Pauli.zGen j).op (basis y) = (if bit j y then (-1 : Zeta8) else 1) • basis y := by
        funext v
        simp only [zGen_op, Pi.smul_apply, smul_eq_mul, basis]
        by_cases hvy : v = y
        · subst hvy; simp
        · simp [hvy]
      have h1 := congrFun (hZ j (basis y)) w
      rw [h2, map_smul, zGen_op] at h1
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      have hv : W (basis y) w = 0 := by
        apply zeta8_eq_zero_of_add_self
        cases hby : bit j y <;> cases hbw : bit j w <;>
          simp only [hby, hbw, Bool.false_eq_true, ↓reduceIte] at hj h1
        · exact absurd rfl hj
        · linear_combination h1
        · linear_combination -h1
        · exact absurd rfl hj
      simp [hv, basis, hwy]
  have hflip : ∀ j y, lam (flipBit j y) = lam y := by
    intro j y
    have h2 : (Pauli.xGen j).op (basis y) = basis (flipBit j y) := by
      funext v
      simp only [xGen_op, basis, flipBit_eq_iff]
    have h1 := congrFun (hX j (basis y)) (flipBit j y)
    rw [h2, hdiag y, hdiag (flipBit j y)] at h1
    simp only [Pi.smul_apply, smul_eq_mul, xGen_op, flipBit_flipBit_self, basis, if_true,
      mul_one] at h1
    exact h1
  refine ⟨lam ⟨0, Nat.two_pow_pos n⟩, fun ψ => ?_⟩
  have hW : W = lam ⟨0, Nat.two_pow_pos n⟩ • LinearMap.id := by
    apply LinearMap.ext_basis
    intro y
    rw [hdiag y, eq_zero_of_flipBit_invariant lam hflip y]
    rfl
  rw [hW]
  rfl

/-! ### Soundness of the checker -/

/-- One direction of the scalar relation between circuits with the same
tableau: `denote (inverse b) ∘ denote a` commutes with every generator. -/
lemma exists_scalar_of_tableau_eq {a b : Circuit n} {T : List Pauli}
    (ha : tableau a = some T) (hb : tableau b = some T) :
    ∃ lam : Zeta8, ∀ ψ, denote (inverse b) (denote a ψ) = lam • ψ := by
  have key := mapOpt_eq_some ha hb
  have hbp := tableau_proper hb
  let W : Vec n →ₗ[Zeta8] Vec n := (denoteₗ (inverse b)).comp (denoteₗ a)
  have hW : ∀ P ∈ generators n, ∀ ψ, W (P.op ψ) = P.op (W ψ) := by
    intro P hP ψ
    obtain ⟨Q, hQa, hQb⟩ := key P hP
    simp only [W, LinearMap.comp_apply, denoteₗ_apply]
    rw [conj_sound hQa]
    have e1 : P.op (denote (inverse b) (denote a ψ)) =
        denote (inverse b) (denote b (P.op (denote (inverse b) (denote a ψ)))) :=
      (denote_inverse_denote b hbp _).symm
    rw [e1, conj_sound hQb, denote_denote_inverse b hbp]
  obtain ⟨lam, hlam⟩ := eq_smul_of_comm_generators W
    (fun j ψ => hW _ (xGen_mem_generators j) ψ) (fun j ψ => hW _ (zGen_mem_generators j) ψ)
  exact ⟨lam, fun ψ => hlam ψ⟩

/-- Equal tableaux certify equivalence up to a unit scalar: the shape of
`NormalForm.sound`, for `≡ₛ`. -/
theorem tableau_sound {a b : Circuit n} {T : List Pauli} (ha : tableau a = some T)
    (hb : tableau b = some T) : a ≡ₛ b := by
  obtain ⟨lam, hlam⟩ := exists_scalar_of_tableau_eq ha hb
  obtain ⟨mu, hmu⟩ := exists_scalar_of_tableau_eq hb ha
  have hap := tableau_proper ha
  have hbp := tableau_proper hb
  have hab : ∀ ψ, denote a ψ = lam • denote b ψ := fun ψ => by
    rw [← denote_smul, ← hlam ψ, denote_denote_inverse b hbp]
  have hunit : lam * mu = 1 := by
    have h2 : (lam * mu) • basis ⟨0, Nat.two_pow_pos n⟩ = basis ⟨0, Nat.two_pow_pos n⟩ := by
      rw [mul_smul, ← hmu, ← denote_smul, ← hab, denote_inverse_denote a hap]
    have := congrFun h2 ⟨0, Nat.two_pow_pos n⟩
    simpa [basis] using this
  exact ⟨lam, ⟨⟨lam, mu, hunit, (mul_comm mu lam).trans hunit⟩, rfl⟩, hab⟩

/-- The tableau check is sound. -/
theorem tableauCheck_sound (a b : Circuit n) (h : tableauCheck a b = true) : a ≡ₛ b := by
  unfold tableauCheck at h
  split at h
  · rename_i ta tb ha hb
    exact tableau_sound ha (by rw [hb, of_decide_eq_true h])
  · exact absurd h Bool.false_ne_true

/-- The Clifford tableau checker: `≡ₛ` on the Clifford fragment, in `O(n)`
bit operations per gate. -/
def tableauChecker (n : ℕ) : ScalarChecker n :=
  ⟨tableauCheck, tableauCheck_sound⟩

/-- The first generator whose images under the two circuits differ, for
diagnosing a `false`; `none` when every generator agrees. -/
def witness (a b : Circuit n) : Option Pauli :=
  (generators n).find? fun P => decide (conj a P ≠ conj b P)

/-! ### Tests

Each equivalence is closed by the checker; `decide +kernel` evaluates the
tableau comparison and the soundness theorem turns the `true` into `≡ₛ`. -/

namespace Tableau.Tests

open Instr

/-- Conjugating a CNOT by `H ⊗ H` reverses it. -/
theorem hh_cnot_hh : ([H 0, H 1, CX 0 1, H 0, H 1] : Circuit 2) ≡ₛ [CX 1 0] :=
  (tableauChecker 2).sound _ _ (by decide +kernel)

/-- The two three-CNOT decompositions of SWAP agree. -/
theorem swap_swap : ([CX 0 1, CX 1 0, CX 0 1] : Circuit 2) ≡ₛ [CX 1 0, CX 0 1, CX 1 0] :=
  (tableauChecker 2).sound _ _ (by decide +kernel)

/-- CZ is symmetric in its two qubits. -/
theorem cz_symm : ([H 1, CX 0 1, H 1] : Circuit 2) ≡ₛ [H 0, CX 1 0, H 0] :=
  (tableauChecker 2).sound _ _ (by decide +kernel)

/-- `S X S† = Y`; as a circuit, `S†` runs first. -/
theorem Sdg_X_S_eq_Y : ([Sdg 0, X 0, S 0] : Circuit 1) ≡ₛ [Y 0] :=
  (tableauChecker 1).sound _ _ (by decide +kernel)

/-- `Z X = −X Z`: equal up to the scalar `−1`, which the tableau ignores. -/
theorem Z_X_scalar_X_Z : ([Z 0, X 0] : Circuit 1) ≡ₛ [X 0, Z 0] :=
  (tableauChecker 1).sound _ _ (by decide +kernel)

/-- `H` and `S` are not equivalent: the check returns `false`. -/
theorem not_H_S : tableauCheck ([H 0] : Circuit 1) [S 0] = false := by decide +kernel

/-- `T` is outside the fragment: the check is `false` even for equal
circuits. -/
theorem not_T_T : tableauCheck ([T 0] : Circuit 1) [T 0] = false := by decide +kernel

/-- The witness for `[H 0]` versus `[S 0]` is the first generator, `X_0`:
`H` sends it to `Z_0`, `S` to `Y_0`. -/
theorem witness_H_S : witness ([H 0] : Circuit 1) [S 0] = some ⟨1, 0, 0⟩ := by decide +kernel

/-- The tableau of `H 0; CX 0 1`: `X_0 ↦ Z_0`, `X_1 ↦ X_1`, `Z_0 ↦ X_0 X_1`,
`Z_1 ↦ Z_0 Z_1`. -/
theorem tableau_H_CX : tableau ([H 0, CX 0 1] : Circuit 2) =
    some [⟨0, 1, 0⟩, ⟨2, 0, 0⟩, ⟨3, 0, 0⟩, ⟨0, 3, 0⟩] := by
  decide +kernel

/-- The three-qubit phase-flip repetition encoder of
`CircuitEq.Benchmarks.Rep3PhaseFlip` (copied here, since a checker module
cannot import the benchmark modules). -/
def rep3Original : Circuit 3 := [CX 0 1, CX 0 2, H 0, H 1, H 2]

/-- Its PyZX output. -/
def rep3Optimized : Circuit 3 := [CX 0 1, H 1, CX 0 2, H 2, H 0]

/-- The benchmark pair, decided by the tableau. -/
theorem rep3 : rep3Original ≡ₛ rep3Optimized :=
  (tableauChecker 3).sound _ _ (by decide +kernel)

/-- The Steane plus-state encoder of `CircuitEq.Benchmarks.SteanePlus`. -/
def steaneOriginal : Circuit 7 :=
  [H 0, H 1, H 3,
    CX 0 2, CX 0 4, CX 0 6, CX 1 2, CX 1 5, CX 1 6, CX 3 4, CX 3 5, CX 3 6,
    H 0, H 1, H 2, H 3, H 4, H 5, H 6]

/-- Its PyZX output. -/
def steaneOptimized : Circuit 7 :=
  [H 2, CX 2 1, CX 2 0, H 4, CX 4 3, CX 4 0,
    H 5, CX 5 3, CX 5 1, H 6, CX 6 3, CX 6 1, CX 6 0]

/-- The benchmark pair, decided by the tableau on seven qubits. -/
theorem steane : steaneOriginal ≡ₛ steaneOptimized :=
  (tableauChecker 7).sound _ _ (by decide +kernel)

end Tableau.Tests

end Quantum.Circuit
