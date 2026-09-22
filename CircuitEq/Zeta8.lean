/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Ring

/-!
# `Zeta8` — the coefficient field ℚ(ζ₈) of Clifford+T

Every matrix entry of a Clifford+T circuit lies in `ℤ[1/√2, i]`, which sits
inside the cyclotomic field `ℚ(ζ₈) = ℚ(i, √2)`. Mathlib's `ℂ` is
noncomputable, so it cannot be the coefficient type of anything the kernel
has to evaluate. This file provides a **computable** model of ℚ(ζ₈) instead,
so that gate identities close by `decide +kernel`.

An element is stored by its coordinates `a + b·ω + c·ω² + d·ω³` in the power
basis of `ω = ζ₈ = e^{iπ/4}`, with `ω⁴ = -1`. Equality is decided
structurally (four rational comparisons), and every ring operation is a
polynomial in the coordinates, so the whole `CommRing` structure is
kernel-reducible.

Useful elements: `ω`, `I = ω²`, `sqrt2 = ω - ω³`, `invSqrt2 = sqrt2 / 2`.

Complex conjugation is `star` (it sends `ω ↦ ω⁻¹ = -ω³`). The embedding into
`ℂ` is deferred; see the README.
-/

namespace Quantum

/-- The cyclotomic field `ℚ(ζ₈)`, stored in the power basis of `ω = ζ₈`:
`⟨a, b, c, d⟩` denotes `a + b·ω + c·ω² + d·ω³`, with `ω⁴ = -1`. -/
@[ext]
structure Zeta8 where
  /-- Coefficient of `1`. -/
  a : ℚ
  /-- Coefficient of `ω`. -/
  b : ℚ
  /-- Coefficient of `ω² = i`. -/
  c : ℚ
  /-- Coefficient of `ω³`. -/
  d : ℚ
  deriving DecidableEq, Repr

namespace Zeta8

/-! ### Ring operations, coordinate-wise -/

instance : Zero Zeta8 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Zeta8 := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Zeta8 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg Zeta8 := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub Zeta8 := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩

/-- Multiplication: the polynomial product in `ω`, reduced by `ω⁴ = -1`. -/
instance : Mul Zeta8 :=
  ⟨fun x y =>
    ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
     x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
     x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
     x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩⟩

instance : NatCast Zeta8 := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : IntCast Zeta8 := ⟨fun n => ⟨n, 0, 0, 0⟩⟩

/-- Complex conjugation: `ω ↦ ω⁻¹ = -ω³`, `ω² ↦ -ω²`, `ω³ ↦ -ω`. -/
instance : Star Zeta8 := ⟨fun x => ⟨x.a, -x.d, -x.c, -x.b⟩⟩

@[simp] lemma zero_a : (0 : Zeta8).a = 0 := rfl
@[simp] lemma zero_b : (0 : Zeta8).b = 0 := rfl
@[simp] lemma zero_c : (0 : Zeta8).c = 0 := rfl
@[simp] lemma zero_d : (0 : Zeta8).d = 0 := rfl
@[simp] lemma one_a : (1 : Zeta8).a = 1 := rfl
@[simp] lemma one_b : (1 : Zeta8).b = 0 := rfl
@[simp] lemma one_c : (1 : Zeta8).c = 0 := rfl
@[simp] lemma one_d : (1 : Zeta8).d = 0 := rfl
@[simp] lemma add_a (x y : Zeta8) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : Zeta8) : (x + y).b = x.b + y.b := rfl
@[simp] lemma add_c (x y : Zeta8) : (x + y).c = x.c + y.c := rfl
@[simp] lemma add_d (x y : Zeta8) : (x + y).d = x.d + y.d := rfl
@[simp] lemma neg_a (x : Zeta8) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : Zeta8) : (-x).b = -x.b := rfl
@[simp] lemma neg_c (x : Zeta8) : (-x).c = -x.c := rfl
@[simp] lemma neg_d (x : Zeta8) : (-x).d = -x.d := rfl
@[simp] lemma sub_a (x y : Zeta8) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b (x y : Zeta8) : (x - y).b = x.b - y.b := rfl
@[simp] lemma sub_c (x y : Zeta8) : (x - y).c = x.c - y.c := rfl
@[simp] lemma sub_d (x y : Zeta8) : (x - y).d = x.d - y.d := rfl
@[simp] lemma mul_a (x y : Zeta8) :
    (x * y).a = x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b := rfl
@[simp] lemma mul_b (x y : Zeta8) :
    (x * y).b = x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c := rfl
@[simp] lemma mul_c (x y : Zeta8) :
    (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d := rfl
@[simp] lemma mul_d (x y : Zeta8) :
    (x * y).d = x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a := rfl
@[simp] lemma natCast_a (n : ℕ) : (n : Zeta8).a = n := rfl
@[simp] lemma natCast_b (n : ℕ) : (n : Zeta8).b = 0 := rfl
@[simp] lemma natCast_c (n : ℕ) : (n : Zeta8).c = 0 := rfl
@[simp] lemma natCast_d (n : ℕ) : (n : Zeta8).d = 0 := rfl
@[simp] lemma intCast_a (n : ℤ) : (n : Zeta8).a = n := rfl
@[simp] lemma intCast_b (n : ℤ) : (n : Zeta8).b = 0 := rfl
@[simp] lemma intCast_c (n : ℤ) : (n : Zeta8).c = 0 := rfl
@[simp] lemma intCast_d (n : ℤ) : (n : Zeta8).d = 0 := rfl
@[simp] lemma star_a (x : Zeta8) : (star x).a = x.a := rfl
@[simp] lemma star_b (x : Zeta8) : (star x).b = -x.d := rfl
@[simp] lemma star_c (x : Zeta8) : (star x).c = -x.c := rfl
@[simp] lemma star_d (x : Zeta8) : (star x).d = -x.b := rfl

/-- The ring axioms are coordinate-wise polynomial identities over `ℚ`. -/
instance : CommRing Zeta8 where
  add := (· + ·)
  add_assoc x y z := by ext <;> simp <;> ring
  zero := 0
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp <;> ring
  mul := (· * ·)
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  one := 1
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  neg := (- ·)
  sub := (· - ·)
  sub_eq_add_neg x y := by ext <;> simp <;> ring
  neg_add_cancel x := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_comm x y := by ext <;> simp <;> ring
  natCast := (↑)
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast := (↑)
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp

/-- Conjugation is a ring involution. -/
instance : StarRing Zeta8 where
  star := star
  star_involutive x := by ext <;> simp
  star_mul x y := by ext <;> simp <;> ring
  star_add x y := by ext <;> simp <;> ring

/-! ### Distinguished elements -/

/-- `ω = ζ₈ = e^{iπ/4}`, the generator of the power basis. -/
def ω : Zeta8 := ⟨0, 1, 0, 0⟩

/-- The imaginary unit `i = ω²`. -/
def I : Zeta8 := ⟨0, 0, 1, 0⟩

/-- `√2 = ω - ω³`. -/
def sqrt2 : Zeta8 := ⟨0, 1, 0, -1⟩

/-- `1/√2 = (ω - ω³)/2`, the Hadamard normalization. -/
def invSqrt2 : Zeta8 := ⟨0, 1/2, 0, -1/2⟩

lemma ω_pow_four : ω ^ 4 = -1 := by decide +kernel
lemma ω_pow_eight : ω ^ 8 = 1 := by decide +kernel
lemma ω_mul_ω : ω * ω = I := by decide +kernel
lemma I_mul_I : I * I = -1 := by decide +kernel
lemma sqrt2_eq : sqrt2 = ω - ω ^ 3 := by decide +kernel
lemma sqrt2_mul_sqrt2 : sqrt2 * sqrt2 = 2 := by decide +kernel
lemma invSqrt2_mul_sqrt2 : invSqrt2 * sqrt2 = 1 := by decide +kernel
lemma two_mul_invSqrt2_mul_invSqrt2 : 2 * (invSqrt2 * invSqrt2) = 1 := by decide +kernel
lemma star_ω : star ω = -ω ^ 3 := by decide +kernel
lemma star_I : star I = -I := by decide +kernel
lemma star_invSqrt2 : star invSqrt2 = invSqrt2 := by decide +kernel

/-! ### Exponents of `ω` live in `Fin 8`

`ω ^ 8 = 1`, so a power of `ω` is named by an exponent modulo eight. Global
phases are carried as `k : Fin 8`, whose addition and negation are already
modular, and these lemmas are what makes phases compose. -/

/-- An exponent of `ω` may be reduced modulo eight. -/
lemma ω_pow_mod (m : ℕ) : ω ^ (m % 8) = ω ^ m := (pow_eq_pow_mod m ω_pow_eight).symm

/-- Exponents in `Fin 8` add: the sum wraps at eight, and so does `ω`. -/
lemma ω_pow_val_add (j k : Fin 8) : ω ^ ((j + k : Fin 8) : ℕ) = ω ^ (j : ℕ) * ω ^ (k : ℕ) := by
  rw [Fin.val_add, ω_pow_mod, pow_add]

/-- The exponent `-k` in `Fin 8` names the inverse of `ω ^ k`. -/
lemma ω_pow_val_neg_mul : ∀ k : Fin 8, ω ^ ((-k : Fin 8) : ℕ) * ω ^ (k : ℕ) = 1 := by
  decide +kernel

end Zeta8

end Quantum
