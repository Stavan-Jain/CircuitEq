/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Zeta8
import CircuitEq.Bits
import CircuitEq.Gates

/-!
# `Dyadic8` — gcd-free amplitudes for the kernel

Every amplitude a Clifford+T circuit produces from a basis state lies in
`ℤ[ω, 1/√2]` (the ring `D[ω]` of exact synthesis): `H` is the only gate with
a denominator, and that denominator is exactly `√2`. `Zeta8` stores four
rationals and normalises each by a gcd on every operation, and profiling
shows that gcd arithmetic is where the kernel spends its time in a
`decide +kernel`. This file is the representation the decision procedure
computes in instead.

`Dyadic8` is four integers `a, b, c, d` and an exponent `k`, denoting

```
(a + b·ω + c·ω² + d·ω³) / √2 ^ k
```

with `ω⁴ = -1`. The operations never divide:

* `mul` multiplies the quadruples as polynomials in `ω` and adds exponents;
* `raise` rewrites `v / √2 ^ k` as `(√2 · v) / √2 ^ (k + 1)`, where
  multiplication by `√2 = ω - ω³` is the signed shuffle
  `(a, b, c, d) ↦ (b - d, a + c, b + d, c - a)`;
* `add` raises the summand with the smaller exponent until the exponents
  agree, then adds coordinate-wise;
* `eqv` aligns the same way and compares the integers.

The representation is not canonical (`⟨2, 0, 0, 0, 2⟩` and `⟨1, 0, 0, 0, 0⟩`
both denote `1`), and nothing here relies on it being so: `eqv` is exact
because multiplication by `√2` is injective, which is what `eqv_iff` proves.
`reduce` divides out `√2` while the coordinates allow it and is available to
keep numbers small; the evaluator does not need it, since the kernel's
integer arithmetic is GMP and a few hundred bits cost nothing.

## Gate actions

`Gate1.matD` and `applyOneD` mirror `Gate1.mat` and `applyOne` entry for
entry, a product per matrix entry. Every entry of a Clifford+T gate is `0`
or a unit monomial `±ω^j`, over `√2` for `H`, so the evaluator runs the
specialised `Gate1.applyD` instead: a diagonal gate is a coordinate shuffle
(`mulω`, `mulI`, …) on the amplitudes with the bit set, `X` and `Y` are the
flip with a shuffle, and `H` is one `add` and an exponent bump, with no
`Dyadic8` product anywhere. `Gate1.applyN` and `applyCNOTN` are the same
actions on `ℕ`-indexed states, definitionally, which is what lets the
kernel memoise the closure evaluator of `CircuitEq.Semantics` (see the
section docstring below).

## Trust

`toZeta8` is the meaning, and `Zeta8` remains the coefficient field of
`denote` and `≡ᵤ`. Every operation comes with its `toZeta8_*` lemma, the
dyadic gate matrices are checked against `Gate1.mat` entry by entry, and
every gate action has a correspondence lemma with `applyOne` or
`applyCNOT`. `CircuitEq/Semantics.lean` builds the evaluators on top and
routes the `Decidable` instances through them, so the kernel never sees a
rational.

## Kernel cost

An integer operation on numerals is one GMP call plus a few reduction
steps for the `Int` constructors; a `Zeta8` product is sixteen `Rat`
products and twelve `Rat` sums, each with a gcd normalisation. A `mul` here
is sixteen integer products and twelve sums; the specialised gate actions
need at most four integer sums (`H`) or none at all (a diagonal gate is a
shuffle with at most one negation). Measurements are in CLAUDE.md,
"Kernel-cost notes".
-/

namespace Quantum

/-- An element of `ℤ[ω, 1/√2]`: `⟨a, b, c, d, k⟩` denotes
`(a + b·ω + c·ω² + d·ω³) / √2 ^ k`, with `ω⁴ = -1`. -/
@[ext]
structure Dyadic8 where
  /-- Numerator coefficient of `1`. -/
  a : ℤ
  /-- Numerator coefficient of `ω`. -/
  b : ℤ
  /-- Numerator coefficient of `ω² = i`. -/
  c : ℤ
  /-- Numerator coefficient of `ω³`. -/
  d : ℤ
  /-- The exponent of `√2` in the denominator. -/
  k : ℕ
  deriving DecidableEq, Repr

namespace Dyadic8

/-! ### Meaning -/

/-- The numerator `a + b·ω + c·ω² + d·ω³` as an element of `ℚ(ζ₈)`. -/
def num (x : Dyadic8) : Zeta8 := ⟨x.a, x.b, x.c, x.d⟩

/-- The value: numerator over `√2 ^ k`. -/
def toZeta8 (x : Dyadic8) : Zeta8 := x.num * Zeta8.invSqrt2 ^ x.k

/-! ### Constants and operations -/

/-- `0`. -/
def zero : Dyadic8 := ⟨0, 0, 0, 0, 0⟩

/-- `1`. -/
def one : Dyadic8 := ⟨1, 0, 0, 0, 0⟩

/-- `ω = ζ₈`. -/
def ω : Dyadic8 := ⟨0, 1, 0, 0, 0⟩

/-- Negation, coordinate-wise on the numerator. -/
def neg (x : Dyadic8) : Dyadic8 := ⟨-x.a, -x.b, -x.c, -x.d, x.k⟩

/-- Multiplication: the polynomial product in `ω` reduced by `ω⁴ = -1`, and
the exponents add. No division anywhere. -/
def mul (x y : Dyadic8) : Dyadic8 :=
  ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
   x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
   x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a,
   x.k + y.k⟩

/-- `ω ^ k`, by repeated multiplication. -/
def ωPow : ℕ → Dyadic8
  | 0 => one
  | k + 1 => mul (ωPow k) ω

/-- Multiplication by `√2 = ω - ω³`, as the signed shuffle of the numerator
`(a, b, c, d) ↦ (b - d, a + c, b + d, c - a)`; the exponent is unchanged. -/
def sqrt2Mul (x : Dyadic8) : Dyadic8 := ⟨x.b - x.d, x.a + x.c, x.b + x.d, x.c - x.a, x.k⟩

/-- The same value with the exponent raised by one: multiply the numerator
by `√2` and the denominator by `√2`. -/
def raise (x : Dyadic8) : Dyadic8 := ⟨x.b - x.d, x.a + x.c, x.b + x.d, x.c - x.a, x.k + 1⟩

/-- `raise`, `j` times. -/
def raiseN (x : Dyadic8) : ℕ → Dyadic8
  | 0 => x
  | j + 1 => raise (raiseN x j)

/-- `x · ω`: the shuffle `(a, b, c, d) ↦ (-d, a, b, c)`. -/
def mulω (x : Dyadic8) : Dyadic8 := ⟨-x.d, x.a, x.b, x.c, x.k⟩

/-- `x · i`, with `i = ω²`: the shuffle `(a, b, c, d) ↦ (-c, -d, a, b)`. -/
def mulI (x : Dyadic8) : Dyadic8 := ⟨-x.c, -x.d, x.a, x.b, x.k⟩

/-- `x · (-i)`: the shuffle `(a, b, c, d) ↦ (c, d, -a, -b)`. -/
def mulNegI (x : Dyadic8) : Dyadic8 := ⟨x.c, x.d, -x.a, -x.b, x.k⟩

/-- `x · (-ω³) = x · ω⁷`: the shuffle `(a, b, c, d) ↦ (b, c, d, -a)`. -/
def mulNegω3 (x : Dyadic8) : Dyadic8 := ⟨x.b, x.c, x.d, -x.a, x.k⟩

/-- `x / √2`: the same numerator over one more power of `√2`. -/
def divSqrt2 (x : Dyadic8) : Dyadic8 := ⟨x.a, x.b, x.c, x.d, x.k + 1⟩

/-- Coordinate-wise sum of two elements that already share an exponent;
the caller aligns (`add` does). -/
def addAligned (x y : Dyadic8) : Dyadic8 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.k⟩

/-- Addition: raise the summand with the smaller exponent until the
exponents agree, then add the numerators. -/
def add (x y : Dyadic8) : Dyadic8 := addAligned (raiseN x (y.k - x.k)) (raiseN y (x.k - y.k))

/-- Numerator equality of two elements that already share an exponent. -/
def eqvAligned (x y : Dyadic8) : Bool :=
  decide (x.a = y.a) && decide (x.b = y.b) && decide (x.c = y.c) && decide (x.d = y.d)

/-- Equality of values: align the exponents, then compare the numerators.
Exact even though the representation is not canonical (`eqv_iff`). -/
def eqv (x y : Dyadic8) : Bool := eqvAligned (raiseN x (y.k - x.k)) (raiseN y (x.k - y.k))

/-- One reduction step: if the numerator is divisible by `√2` (which holds
iff `a ≡ c` and `b ≡ d` mod 2) and the exponent is positive, divide both.
`none` when no step applies. -/
def reduceStep (x : Dyadic8) : Option Dyadic8 :=
  match x.k with
  | 0 => none
  | k + 1 =>
    if (x.a + x.c) % 2 = 0 && (x.b + x.d) % 2 = 0 then
      some ⟨(x.b - x.d) / 2, (x.a + x.c) / 2, (x.b + x.d) / 2, (x.c - x.a) / 2, k⟩
    else none

/-- Reduce as far as `fuel` steps allow. -/
def reduceAux : ℕ → Dyadic8 → Dyadic8
  | 0, x => x
  | j + 1, x =>
    match reduceStep x with
    | some y => reduceAux j y
    | none => x

/-- Divide out `√2` while the numerator allows it. The exponent can drop at
most `k` times, so `k` is enough fuel. Optional: `eqv` does not rely on it. -/
def reduce (x : Dyadic8) : Dyadic8 := reduceAux x.k x

/-! ### Exponents and numerators of the operations -/

/-- `neg` keeps the exponent. -/
@[simp] lemma k_neg (x : Dyadic8) : (neg x).k = x.k := rfl
/-- `mul` adds the exponents. -/
@[simp] lemma k_mul (x y : Dyadic8) : (mul x y).k = x.k + y.k := rfl
/-- `sqrt2Mul` keeps the exponent. -/
@[simp] lemma k_sqrt2Mul (x : Dyadic8) : (sqrt2Mul x).k = x.k := rfl
/-- `raise` bumps the exponent. -/
@[simp] lemma k_raise (x : Dyadic8) : (raise x).k = x.k + 1 := rfl
/-- `mulω` keeps the exponent. -/
@[simp] lemma k_mulω (x : Dyadic8) : (mulω x).k = x.k := rfl
/-- `mulI` keeps the exponent. -/
@[simp] lemma k_mulI (x : Dyadic8) : (mulI x).k = x.k := rfl
/-- `mulNegI` keeps the exponent. -/
@[simp] lemma k_mulNegI (x : Dyadic8) : (mulNegI x).k = x.k := rfl
/-- `mulNegω3` keeps the exponent. -/
@[simp] lemma k_mulNegω3 (x : Dyadic8) : (mulNegω3 x).k = x.k := rfl
/-- `divSqrt2` bumps the exponent. -/
@[simp] lemma k_divSqrt2 (x : Dyadic8) : (divSqrt2 x).k = x.k + 1 := rfl
/-- `addAligned` keeps the first exponent. -/
@[simp] lemma k_addAligned (x y : Dyadic8) : (addAligned x y).k = x.k := rfl

/-- `raiseN x j` raises the exponent by `j`. -/
@[simp] lemma k_raiseN (x : Dyadic8) (j : ℕ) : (raiseN x j).k = x.k + j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [raiseN, ih, Nat.add_assoc]

/-- The numerator of `neg`. -/
lemma num_neg (x : Dyadic8) : num (neg x) = -num x := by ext <;> simp [num, neg]

/-- The numerator of `mul` is the `Zeta8` product of the numerators. -/
lemma num_mul (x y : Dyadic8) : num (mul x y) = num x * num y := by
  ext <;> simp [num, mul]

/-- The numerator of `sqrt2Mul`: the shuffle is multiplication by `√2`. -/
lemma num_sqrt2Mul (x : Dyadic8) : num (sqrt2Mul x) = Zeta8.sqrt2 * num x := by
  ext <;> simp [num, sqrt2Mul, Zeta8.sqrt2] <;> ring

/-- The numerator of `raise`: the shuffle is multiplication by `√2`. -/
lemma num_raise (x : Dyadic8) : num (raise x) = Zeta8.sqrt2 * num x := by
  ext <;> simp [num, raise, Zeta8.sqrt2] <;> ring

/-- The numerator of `mulω`. -/
lemma num_mulω (x : Dyadic8) : num (mulω x) = Zeta8.ω * num x := by
  ext <;> simp [num, mulω, Zeta8.ω]

/-- The numerator of `mulI`. -/
lemma num_mulI (x : Dyadic8) : num (mulI x) = Zeta8.I * num x := by
  ext <;> simp [num, mulI, Zeta8.I]

/-- The numerator of `mulNegI`. -/
lemma num_mulNegI (x : Dyadic8) : num (mulNegI x) = -Zeta8.I * num x := by
  ext <;> simp [num, mulNegI, Zeta8.I]

/-- The numerator of `mulNegω3`. -/
lemma num_mulNegω3 (x : Dyadic8) : num (mulNegω3 x) = -Zeta8.ω ^ 3 * num x := by
  ext <;> simp [num, mulNegω3, Zeta8.ω, pow_succ]

/-- `divSqrt2` keeps the numerator. -/
lemma num_divSqrt2 (x : Dyadic8) : num (divSqrt2 x) = num x := rfl

/-- The numerator of `addAligned` is the sum of the numerators. -/
lemma num_addAligned (x y : Dyadic8) : num (addAligned x y) = num x + num y := by
  ext <;> simp [num, addAligned]

/-! ### The meaning of the operations -/

/-- `zero` means `0`. -/
@[simp] lemma toZeta8_zero : toZeta8 zero = 0 := by decide +kernel

/-- `one` means `1`. -/
@[simp] lemma toZeta8_one : toZeta8 one = 1 := by decide +kernel

/-- `ω` means `Zeta8.ω`. -/
@[simp] lemma toZeta8_ω : toZeta8 ω = Zeta8.ω := by decide +kernel

/-- `neg` means negation. -/
lemma toZeta8_neg (x : Dyadic8) : toZeta8 (neg x) = -toZeta8 x := by
  simp [toZeta8, num_neg]

/-- `mul` means multiplication. -/
lemma toZeta8_mul (x y : Dyadic8) : toZeta8 (mul x y) = toZeta8 x * toZeta8 y := by
  simp only [toZeta8, num_mul, k_mul, pow_add]
  ring

/-- `sqrt2Mul` means multiplication by `√2`. -/
lemma toZeta8_sqrt2Mul (x : Dyadic8) : toZeta8 (sqrt2Mul x) = Zeta8.sqrt2 * toZeta8 x := by
  simp only [toZeta8, num_sqrt2Mul, k_sqrt2Mul, mul_assoc]

/-- Raising the exponent does not change the value: `√2 / √2 = 1`. -/
lemma toZeta8_raise (x : Dyadic8) : toZeta8 (raise x) = toZeta8 x := by
  simp only [toZeta8, num_raise, k_raise, pow_succ]
  calc Zeta8.sqrt2 * num x * (Zeta8.invSqrt2 ^ x.k * Zeta8.invSqrt2)
      = num x * Zeta8.invSqrt2 ^ x.k * (Zeta8.invSqrt2 * Zeta8.sqrt2) := by ring
    _ = num x * Zeta8.invSqrt2 ^ x.k := by rw [Zeta8.invSqrt2_mul_sqrt2, mul_one]

/-- `mulω` means multiplication by `ω`. -/
lemma toZeta8_mulω (x : Dyadic8) : toZeta8 (mulω x) = Zeta8.ω * toZeta8 x := by
  simp only [toZeta8, num_mulω, k_mulω, mul_assoc]

/-- `mulI` means multiplication by `i`. -/
lemma toZeta8_mulI (x : Dyadic8) : toZeta8 (mulI x) = Zeta8.I * toZeta8 x := by
  simp only [toZeta8, num_mulI, k_mulI, mul_assoc]

/-- `mulNegI` means multiplication by `-i`. -/
lemma toZeta8_mulNegI (x : Dyadic8) : toZeta8 (mulNegI x) = -Zeta8.I * toZeta8 x := by
  simp only [toZeta8, num_mulNegI, k_mulNegI, mul_assoc]

/-- `mulNegω3` means multiplication by `-ω³`. -/
lemma toZeta8_mulNegω3 (x : Dyadic8) : toZeta8 (mulNegω3 x) = -Zeta8.ω ^ 3 * toZeta8 x := by
  simp only [toZeta8, num_mulNegω3, k_mulNegω3, mul_assoc]

/-- `divSqrt2` means multiplication by `1/√2`. -/
lemma toZeta8_divSqrt2 (x : Dyadic8) : toZeta8 (divSqrt2 x) = Zeta8.invSqrt2 * toZeta8 x := by
  simp only [toZeta8, num_divSqrt2, k_divSqrt2, pow_succ]
  ring

/-- Raising the exponent any number of times does not change the value. -/
lemma toZeta8_raiseN (x : Dyadic8) (j : ℕ) : toZeta8 (raiseN x j) = toZeta8 x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [raiseN, toZeta8_raise, ih]

/-- On aligned exponents, `addAligned` means addition. -/
lemma toZeta8_addAligned {x y : Dyadic8} (h : x.k = y.k) :
    toZeta8 (addAligned x y) = toZeta8 x + toZeta8 y := by
  simp only [toZeta8, num_addAligned, k_addAligned, ← h, add_mul]

/-- `add` means addition. -/
lemma toZeta8_add (x y : Dyadic8) : toZeta8 (add x y) = toZeta8 x + toZeta8 y := by
  unfold add
  rw [toZeta8_addAligned (by simp only [k_raiseN]; omega), toZeta8_raiseN, toZeta8_raiseN]

/-- `ωPow k` means `ω ^ k`. -/
lemma toZeta8_ωPow (k : ℕ) : toZeta8 (ωPow k) = Zeta8.ω ^ k := by
  induction k with
  | zero => simp [ωPow]
  | succ k ih => rw [ωPow, pow_succ, ← ih, ← toZeta8_ω]; exact toZeta8_mul _ _

/-- A reduction step preserves the value: the new element, raised once, is
the old one coordinate by coordinate. -/
lemma toZeta8_of_reduceStep {x y : Dyadic8} (h : reduceStep x = some y) :
    toZeta8 y = toZeta8 x := by
  unfold reduceStep at h
  split at h
  · exact absurd h (by simp)
  · rename_i k _
    split at h
    · rename_i hmod
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hmod
      obtain ⟨hac, hbd⟩ := hmod
      obtain rfl := Option.some.inj h
      have hx :
          raise ⟨(x.b - x.d) / 2, (x.a + x.c) / 2, (x.b + x.d) / 2, (x.c - x.a) / 2, k⟩ = x := by
        ext <;> simp only [raise] <;> omega
      exact (toZeta8_raise _).symm.trans (congrArg toZeta8 hx)
    · exact absurd h (by simp)

/-- Reduction steps preserve the value. -/
lemma toZeta8_reduceAux (j : ℕ) (x : Dyadic8) : toZeta8 (reduceAux j x) = toZeta8 x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    unfold reduceAux
    split
    · rename_i y hy
      rw [ih, toZeta8_of_reduceStep hy]
    · rfl

/-- `reduce` preserves the value. -/
lemma toZeta8_reduce (x : Dyadic8) : toZeta8 (reduce x) = toZeta8 x := toZeta8_reduceAux _ _

/-! ### Equality -/

/-- On aligned elements, numerator equality is value equality: `√2 ^ k` is a
unit, so it cancels, and `{1, ω, ω², ω³}` is a basis of `ℚ(ζ₈)`, so equal
values have equal rational coordinates, hence equal integer ones. -/
lemma eqvAligned_iff {x y : Dyadic8} (h : x.k = y.k) :
    eqvAligned x y = true ↔ toZeta8 x = toZeta8 y := by
  simp only [eqvAligned, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
    rw [Dyadic8.ext ha hb hc hd h]
  · intro hxy
    have hnum : num x = num y := by
      have := congrArg (· * Zeta8.sqrt2 ^ x.k) hxy
      simpa only [toZeta8, ← h, mul_assoc, ← mul_pow, Zeta8.invSqrt2_mul_sqrt2, one_pow,
        mul_one] using this
    simp only [num, Zeta8.ext_iff, Int.cast_inj] at hnum
    exact ⟨⟨⟨hnum.1, hnum.2.1⟩, hnum.2.2.1⟩, hnum.2.2.2⟩

/-- `eqv` decides equality of values exactly. -/
theorem eqv_iff (x y : Dyadic8) : eqv x y = true ↔ toZeta8 x = toZeta8 y := by
  unfold eqv
  rw [eqvAligned_iff (by simp only [k_raiseN]; omega), toZeta8_raiseN, toZeta8_raiseN]

end Dyadic8

namespace Circuit

open Dyadic8

/-- A single-qubit matrix with dyadic entries. -/
abbrev Mat1D := Bool → Bool → Dyadic8

/-- The `ℚ(ζ₈)` matrix of a dyadic matrix. -/
def Mat1D.toMat (G : Mat1D) : Mat1 := Matrix.of fun r c => toZeta8 (G r c)

/-- Entries of `Mat1D.toMat`. -/
@[simp] lemma Mat1D.toMat_apply (G : Mat1D) (r c : Bool) : G.toMat r c = toZeta8 (G r c) := rfl

namespace Gate1

/-- The dyadic matrix of each gate: `Gate1.mat` with `1/√2` as
`⟨1, 0, 0, 0, 1⟩`, `i` as `⟨0, 0, 1, 0, 0⟩` and `-ω³` as `⟨0, 0, 0, -1, 0⟩`. -/
def matD : Gate1 → Mat1D
  | H => fun r c => if r && c then ⟨-1, 0, 0, 0, 1⟩ else ⟨1, 0, 0, 0, 1⟩
  | X => fun r c => if r = c then zero else one
  | Y => fun r c => if r = c then zero else if r then ⟨0, 0, 1, 0, 0⟩ else ⟨0, 0, -1, 0, 0⟩
  | Z => fun r c => if r = c then (if r then ⟨-1, 0, 0, 0, 0⟩ else one) else zero
  | S => fun r c => if r = c then (if r then ⟨0, 0, 1, 0, 0⟩ else one) else zero
  | Sdg => fun r c => if r = c then (if r then ⟨0, 0, -1, 0, 0⟩ else one) else zero
  | T => fun r c => if r = c then (if r then ω else one) else zero
  | Tdg => fun r c => if r = c then (if r then ⟨0, 0, 0, -1, 0⟩ else one) else zero

/-- The dyadic matrices mean the `ℚ(ζ₈)` ones, entry by entry. -/
lemma toZeta8_matD (g : Gate1) (r c : Bool) : toZeta8 (g.matD r c) = g.mat r c := by
  cases g <;> cases r <;> cases c <;> decide +kernel

/-- The dyadic matrices mean the `ℚ(ζ₈)` ones. -/
lemma toMat_matD (g : Gate1) : g.matD.toMat = g.mat :=
  Matrix.ext fun r c => toZeta8_matD g r c

end Gate1

/-- Amplitude vectors with dyadic entries. -/
abbrev VecD (n : ℕ) := Fin (2 ^ n) → Dyadic8

variable {n : ℕ}

/-- `applyOne` on dyadic states: the new amplitude at `x` mixes the old ones
at `x` and at `x` with bit `i` flipped, weighted by row `bit i x` of `G`. -/
def applyOneD (G : Mat1D) (i : Fin n) (ψ : VecD n) : VecD n :=
  fun x => add (mul (G (bit i x) (bit i x)) (ψ x)) (mul (G (bit i x) (!bit i x)) (ψ (flipBit i x)))

/-- `applyCNOT` on dyadic states: a permutation of amplitudes, no arithmetic. -/
def applyCNOTD (c t : Fin n) (ψ : VecD n) : VecD n :=
  fun x => if bit c x then ψ (flipBit t x) else ψ x

/-- `applyOneD` means `applyOne`. -/
lemma toZeta8_comp_applyOneD (G : Mat1D) (i : Fin n) (ψ : VecD n) :
    toZeta8 ∘ applyOneD G i ψ = applyOne G.toMat i (toZeta8 ∘ ψ) := by
  funext x
  simp [applyOneD, applyOne, toZeta8_add, toZeta8_mul]

/-- `applyCNOTD` means `applyCNOT`. -/
lemma toZeta8_comp_applyCNOTD (c t : Fin n) (ψ : VecD n) :
    toZeta8 ∘ applyCNOTD c t ψ = applyCNOT c t (toZeta8 ∘ ψ) := by
  funext x
  simp only [Function.comp_apply, applyCNOTD, applyCNOT]
  split_ifs <;> rfl

/-! ### The gate actions the evaluator runs

`applyOneD` with `Gate1.matD` is the general form, a product per matrix
entry. Every entry of a Clifford+T gate is `0` or a unit monomial `±ω^j`,
over `√2` for `H`, so multiplying an amplitude by an entry is a signed
coordinate shuffle and the zero entries need not be touched at all.
`Gate1.applyD` is that specialisation, one case per gate: a diagonal gate
is a shuffle on the amplitudes with the bit set, `X` and `Y` are the flip
with a shuffle, and `H` is one `add` and an exponent bump. It is proved
against `applyOne g.mat` directly. -/

namespace Gate1

/-- The dyadic action of gate `g` on qubit `i`, specialised per gate; no
`Dyadic8` product anywhere. -/
def applyD : Gate1 → Fin n → VecD n → VecD n
  | H, i, ψ => fun x => divSqrt2 (add (if bit i x then neg (ψ x) else ψ x) (ψ (flipBit i x)))
  | X, i, ψ => fun x => ψ (flipBit i x)
  | Y, i, ψ => fun x => if bit i x then mulI (ψ (flipBit i x)) else mulNegI (ψ (flipBit i x))
  | Z, i, ψ => fun x => if bit i x then neg (ψ x) else ψ x
  | S, i, ψ => fun x => if bit i x then mulI (ψ x) else ψ x
  | Sdg, i, ψ => fun x => if bit i x then mulNegI (ψ x) else ψ x
  | T, i, ψ => fun x => if bit i x then mulω (ψ x) else ψ x
  | Tdg, i, ψ => fun x => if bit i x then mulNegω3 (ψ x) else ψ x

/-- `Gate1.applyD` means `applyOne` with the gate's matrix. -/
lemma toZeta8_comp_applyD (g : Gate1) (i : Fin n) (ψ : VecD n) :
    toZeta8 ∘ g.applyD i ψ = applyOne g.mat i (toZeta8 ∘ ψ) := by
  funext x
  cases g <;> cases hb : bit i x <;>
    simp [applyD, applyOne, mat, hb, toZeta8_add, toZeta8_neg, toZeta8_mulI, toZeta8_mulNegI,
      toZeta8_mulω, toZeta8_mulNegω3, toZeta8_divSqrt2] <;> ring

end Gate1

/-! ### States indexed by `ℕ`

The evaluator the `Decidable` instances run keeps a state as a closure
`ℕ → Dyadic8` rather than as a list or a `Fin`-indexed function. The kernel
memoises `whnf` by structural equality of terms, so a read `ψ 5` of a
closure is one cache lookup once it has been computed, and a gate
application costs one step per amplitude with no list traversal. Two
things defeat that cache, and both are avoided here.

* The index must be a numeral. A `Fin (2 ^ n)` value carries a proof term
  that differs between derivations of the same index (`flipBit i (flipBit i
  x)` against `x`), so closure evaluation over `Fin` recomputes
  exponentially, which is why `denote` itself is never evaluated.
* The index must be *forced*. The kernel substitutes arguments unevaluated,
  so a read `ψ (x ^^^ 2 ^ i)` is keyed by that term, not by its value, and
  every flipping gate doubles the number of distinct keys for one
  amplitude. The only place the kernel replaces a variable by an evaluated
  value is an iota reduction, so `VecN.at` reads through a `match` on the
  index, which turns any index term into the one canonical key for its
  value.

The `ℕ` actions are the `Fin` ones read through `Fin.val`, up to `VecN.at`
unfolding (`Gate1.applyN_val`, `applyCNOTN_val`), so their meaning is
inherited. -/

/-- A dyadic state indexed by the basis index as a number. -/
abbrev VecN := ℕ → Dyadic8

/-- Read `ψ` at `x`, forcing `x` to a numeral first: the `match` makes the
kernel evaluate the index before substituting it, so every read of one
amplitude has the same cache key (see the section docstring). -/
def VecN.at (ψ : VecN) (x : ℕ) : Dyadic8 :=
  match x with
  | 0 => ψ 0
  | k + 1 => ψ (k + 1)

/-- `VecN.at` is application. -/
@[simp] lemma VecN.at_eq (ψ : VecN) (x : ℕ) : ψ.at x = ψ x := by
  cases x <;> rfl

/-- The dyadic action of gate `g` on qubit `i` of an `ℕ`-indexed state:
`Gate1.applyD` with `Nat.testBit` for `bit`, `xor` for `flipBit`, and
forced reads. -/
def Gate1.applyN : Gate1 → ℕ → VecN → VecN
  | .H, i, ψ => fun x =>
      divSqrt2 (add (if x.testBit i then neg (ψ.at x) else ψ.at x) (ψ.at (x ^^^ 2 ^ i)))
  | .X, i, ψ => fun x => ψ.at (x ^^^ 2 ^ i)
  | .Y, i, ψ => fun x =>
      if x.testBit i then mulI (ψ.at (x ^^^ 2 ^ i)) else mulNegI (ψ.at (x ^^^ 2 ^ i))
  | .Z, i, ψ => fun x => if x.testBit i then neg (ψ.at x) else ψ.at x
  | .S, i, ψ => fun x => if x.testBit i then mulI (ψ.at x) else ψ.at x
  | .Sdg, i, ψ => fun x => if x.testBit i then mulNegI (ψ.at x) else ψ.at x
  | .T, i, ψ => fun x => if x.testBit i then mulω (ψ.at x) else ψ.at x
  | .Tdg, i, ψ => fun x => if x.testBit i then mulNegω3 (ψ.at x) else ψ.at x

/-- CNOT on an `ℕ`-indexed state: `applyCNOTD` through `Fin.val`, with
forced reads. -/
def applyCNOTN (c t : ℕ) (ψ : VecN) : VecN :=
  fun x => if x.testBit c then ψ.at (x ^^^ 2 ^ t) else ψ.at x

/-- On indices below `2 ^ n`, `Gate1.applyN` is `Gate1.applyD`. -/
lemma Gate1.applyN_val (g : Gate1) (i : Fin n) (ψ : VecN) (x : Fin (2 ^ n)) :
    g.applyN i ψ x = g.applyD i (ψ ∘ Fin.val) x := by
  cases g <;> simp only [Gate1.applyN, Gate1.applyD, VecN.at_eq] <;> rfl

/-- On indices below `2 ^ n`, `applyCNOTN` is `applyCNOTD`. -/
lemma applyCNOTN_val (c t : Fin n) (ψ : VecN) (x : Fin (2 ^ n)) :
    applyCNOTN c t ψ x = applyCNOTD c t (ψ ∘ Fin.val) x := by
  simp only [applyCNOTN, applyCNOTD, VecN.at_eq]
  rfl

end Circuit

end Quantum
