/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Structural
import CircuitEq.Support
import CircuitEq.Checker
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Phase polynomials: a canonical form for CNOT-plus-diagonal circuits

A circuit of CNOTs and diagonal gates (`Z`, `S`, `S†`, `T`, `T†`) sends each
basis state `|y⟩` to `ω ^ φ(y) |A y⟩`, where `A` is an invertible
`𝔽₂`-linear map and `φ : 𝔽₂ⁿ → ℤ/8` is the *phase function*. Both are read
off the circuit in one pass with no state vector: a CNOT `c t` replaces row
`t` of `A` by `row t ⊕ row c`, and a diagonal gate of phase `k` on wire `i`
adds `k · (m · y)` to `φ`, where `m` is the parity wire `i` currently holds.
This is the representation T-count optimisers work in, and the checker
decides a pair symbolically at a cost linear in the gate count and
independent of `2 ^ n`.

## The form is canonical

The phase function is stored as its *multilinear polynomial* over `ℤ/8`,
`φ(y) = Σ_S a_S ∏_{i ∈ S} y_i`, whose coefficients are unique (Möbius
inversion over the Boolean lattice), so two circuits of the fragment with
the same unitary have the same form and `check` is a decision procedure.
The earlier form, the coefficient vector in the *parity* basis
`{m · y}`, was not: over `ℤ/8` the parity functions are linearly dependent
(`Z` on `a ⊕ b` is `Z a · Z b`; on four wires a `T` on each of the fifteen
parities is the identity), and PyZX's rewrites move phases along exactly
those relations, which the scale test (`benchmarks/scale/`) exposed at
twenty qubits.

Because `2³ ≡ 0 (mod 8)` the polynomial has degree at most three: a parity
term `k · (m · y)` expands, by `s mod 2 ≡ s − 2·C(s,2) + 4·C(s,3) (mod 8)`
for `s = |m ∩ y|`, into `k · yᵢ` on each wire of `m`, `−2k · yᵢ yⱼ` on each
pair and `4k · yᵢ yⱼ yₗ` on each triple. So a form is

* `rows : List ℕ`, one bitmask per wire in the encoding of
  `CircuitEq.Support` (bit `j` of `rows[i]` is set iff input `j` is in the
  parity wire `i` holds);
* `deg1`, `deg2`, `deg3 : Lanes`, the coefficients of the monomials of
  each degree as *bit planes*: three `Nat`s whose bit `t` are the three
  bits of the residue in lane `t`. Lane `i` holds `a_i`, lane `n·i + j`
  (for `i < j`) holds `a_{ij}`, lane `n²·i + n·j + l` (for `i < j < l`)
  holds `a_{ijl}`; every other lane is zero.

A diagonal gate is up to three plane additions: `Lanes.addOn` adds a
constant on every lane of a mask by a three-bit ripple-carry adder on
planes, a fixed number of `Nat` bit operations however many lanes the mask
names, and the masks of the pairs and triples inside `m` (`pairMask`,
`tripMask`) are one shift-and-or per set bit of `m` (`maskFold`). Phases are
in units of `π/4`: `T = 1`, `S = 2`, `Z = 4`, `S† = 6`, `T† = 7`.

`PhasePoly.nf` is the normaliser: `none` at the first gate outside the
fragment, including a CNOT whose control is its target (not unitary).
`phasePolyNormalForm n` packages it as a `NormalForm n` and
`phasePolyChecker n` is its checker; `phasePolyRefutes` is the other
direction, a `Bool` whose `true` proves `¬ a ≡ᵤ b`.

## Soundness and completeness

The invariant is on basis vectors: `PhasePoly.act P y` is
`ω ^ φ(y) • basis (A y)`, with `A y` read from the rows (`linFin`, bit `i`
the parity of `rows[i] &&& y`) and `φ(y)` the polynomial evaluated at `y`
(`phaseAt`, sums over `Finset.range` in `ZMod 8`, never evaluated by the
kernel). `phaseAt_diag` is the heart: the plane additions add exactly
`k · (m · y)`, by the lane lemmas `Lanes.lane_addOn`, the mask lemmas
`testBit_pairMask` and `testBit_tripMask`, and the count identity
`cnt_parity` (`cnt1 − 2·cnt2 + 4·cnt3 = parity` in `ZMod 8`, by induction
on the wires). `run_sound` then tracks `Instr.apply` step by step and
`sound` closes with `equivalent_iff_basis`.

Completeness (`complete`): equal unitaries give equal forms, because the
action on `|y⟩` determines `A y` and `φ(y)`, `A` on the unit vectors
determines the rows, and `φ` on the inputs of weight one, two and three
determines the coefficients degree by degree (`phaseAt_two_pow` and its
two companions), while `Lanes.ext_of_lane` and the support invariant
`Supported` (only the lanes of monomials are ever non-zero) turn equal
coefficients into equal planes. So `phasePolyRefutes a b = true`, which is
"both in the fragment and different forms", proves `¬ a ≡ᵤ b`
(`refutes_sound`), and for the fragment `false` from the checker is a
refutation, not merely "undecided".

## Kernel cost

`nf` is structural recursion over the circuit with `Nat` bit operations
(`^^^`, `&&&`, `|||`, `<<<`, `>>>`, `testBit`, `gcd`, all GMP-accelerated
in the kernel). Nothing of size `2 ^ n` is built; the planes are `n`,
`C(n,2)` and `C(n,3)` bits and the rows `n²` bits. A CNOT is a shift and an
xor. A phase gate builds the pair and triple masks of its parity with
`maskFold`, which visits only the set bits of a sparse parity
(`sparseFold`: lowest set bit by `gcd`, its index by a population count
checked on the 1024 powers of two below the word width) and tests every
index of a dense one (`bitFold`), and skips a plane it would add nothing
to (`Lanes.addOnz`). Measured on an Apple M4 with cached imports
(`benchmarks/scale/README.md`), each pair with a gate-deleted mutant
refuted: random CNOT-plus-`T` circuits of 200, 400 and 800 gates on 20, 40
and 80 wires against their PyZX phase-folded forms in 0.2, 0.6 and 1.9 s of
kernel time at 1.9, 2.0 and 2.5 GB peak (the imports alone are 1.8 GB);
networks of CCZ gadgets, every parity of weight at most three, of 3400,
6800 and 10200 gates on 100, 200 and 300 wires in 2.8, 5.9 and 10.1 s at
2.7, 3.8 and 5.3 GB. What grows is the triple plane: 164 KB at 200 wires,
and the kernel copies it at every gate that changes it. Two traps found on
the way, both about what the kernel retains or re-walks rather than about
arithmetic: a row table kept as a `List ℕ` cost 1.5 MB of retained terms
per CNOT, and a plane passed through unchanged *inside* `add` made every
later gate re-walk the chain of pass-through terms, quadratic time (see
`Lanes.addOnz`). Use `decide +kernel`; the elaborator's own evaluator (bare
`decide`, `rfl`) exhausts the default heartbeat limit at about a hundred
gates.
-/

namespace Quantum.Circuit

open Finset

variable {n : ℕ}

/-! ### Phases and basis vectors -/

/-- `ω ^ k` for a phase `k : ZMod 8`, in units of `π/4`. -/
def ωpow (k : ZMod 8) : Zeta8 := Zeta8.ω ^ k.val

/-- The zero phase is the scalar `1`. -/
@[simp] lemma ωpow_zero : ωpow 0 = 1 := by simp [ωpow]

/-- Phases add modulo 8 because `ω ^ 8 = 1`. -/
lemma ωpow_add (a b : ZMod 8) : ωpow (a + b) = ωpow a * ωpow b := by
  unfold ωpow
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 8]
  rw [pow_add, pow_mul, Zeta8.ω_pow_eight, one_pow, mul_one]

/-- `ω` has order eight: distinct phases give distinct scalars. -/
lemma ωpow_injective : Function.Injective ωpow := by
  intro a b h
  revert a b
  decide +kernel

/-- No phase is the scalar `0`. -/
lemma ωpow_ne_zero (k : ZMod 8) : ωpow k ≠ 0 := by
  revert k
  decide +kernel

/-- The phase of a diagonal gate `diag(1, ω ^ k)`, in units of `π/4`; `none`
for `H`, `X`, `Y`. -/
def Gate1.phase? : Gate1 → Option (ZMod 8)
  | .T => some 1
  | .S => some 2
  | .Z => some 4
  | .Sdg => some 6
  | .Tdg => some 7
  | .H | .X | .Y => none

/-- A gate has a phase iff it is diagonal. -/
lemma Gate1.phase?_isSome (g : Gate1) : g.phase?.isSome = g.isDiag := by
  cases g <;> rfl

/-- A gate with a phase is diagonal. -/
lemma Gate1.isDiag_of_phase? {g : Gate1} {k : ZMod 8} (h : g.phase? = some k) :
    g.isDiag = true := by
  rw [← Gate1.phase?_isSome, h]; rfl

/-- The diagonal of a gate with phase `k` is `(1, ω ^ k)`. -/
lemma Gate1.mat_diag_of_phase? {g : Gate1} {k : ZMod 8} (h : g.phase? = some k) (b : Bool) :
    g.mat b b = ωpow (if b then k else 0) := by
  cases g <;> simp only [Gate1.phase?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    cases b <;> decide +kernel

/-- Two basis indices with the same bits are equal. -/
lemma eq_of_bit_eq {x x' : Fin (2 ^ n)} (h : ∀ i : Fin n, bit i x = bit i x') : x = x' := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact h ⟨j, hj⟩
  · have hn : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt hn),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le x'.isLt hn)]

/-- `flipBit` is an involution, as an equation solver. -/
lemma flipBit_eq_iff {i : Fin n} {x y : Fin (2 ^ n)} : flipBit i x = y ↔ x = flipBit i y :=
  ⟨fun h => by rw [← h, flipBit_flipBit_self], fun h => by rw [h, flipBit_flipBit_self]⟩

/-- A CNOT sends a basis vector to a basis vector. -/
lemma applyCNOT_basis {c t : Fin n} (hct : c ≠ t) (y : Fin (2 ^ n)) :
    applyCNOT c t (basis y) = basis (if bit c y then flipBit t y else y) := by
  funext x
  simp only [applyCNOT, basis]
  cases hcx : bit c x <;> cases hcy : bit c y <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case false.true =>
    have h1 : x ≠ y := fun e => by
      rw [e, hcy] at hcx; exact Bool.false_ne_true hcx.symm
    have h2 : x ≠ flipBit t y := fun e => by
      rw [e, bit_flipBit_of_ne hct, hcy] at hcx; exact Bool.false_ne_true hcx.symm
    rw [if_neg h1, if_neg h2]
  case true.false =>
    have h1 : flipBit t x ≠ y := fun e => by
      rw [← e, bit_flipBit_of_ne hct, hcx] at hcy; exact Bool.false_ne_true hcy.symm
    have h2 : x ≠ y := fun e => by
      rw [e, hcy] at hcx; exact Bool.false_ne_true hcx
    rw [if_neg h1, if_neg h2]
  case true.true => simp only [flipBit_eq_iff]

/-- A diagonal gate scales a basis vector by its diagonal entry. -/
lemma applyOne_basis_of_diag {G : Mat1} (hG : ∀ b, G b (!b) = 0) (i : Fin n) (y : Fin (2 ^ n)) :
    applyOne G i (basis y) = G (bit i y) (bit i y) • basis y := by
  funext x
  rw [applyOne_of_diag hG, Pi.smul_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy; rfl
  · simp [basis, hxy]

/-! ### Bit planes

A `Lanes` is a vector of residues modulo 8 indexed by `ℕ`, stored as three
bit planes: bit `t` of `p0`, `p1`, `p2` are the three bits of lane `t`.
Adding a constant on every lane of a mask is a three-bit ripple-carry adder
on the planes, a fixed number of `Nat` bit operations. -/

/-- Residues modulo 8, one per lane, as three bit planes. -/
structure Lanes where
  /-- Bit `0` of every lane. -/
  p0 : ℕ
  /-- Bit `1` of every lane. -/
  p1 : ℕ
  /-- Bit `2` of every lane. -/
  p2 : ℕ
  deriving DecidableEq, Repr

namespace Lanes

/-- Every lane zero. -/
def zero : Lanes := ⟨0, 0, 0⟩

/-- Lane-wise addition modulo 8: a ripple-carry adder on the planes. -/
def add (a b : Lanes) : Lanes :=
  ⟨a.p0 ^^^ b.p0, a.p1 ^^^ b.p1 ^^^ (a.p0 &&& b.p0),
    a.p2 ^^^ b.p2 ^^^ ((a.p1 &&& b.p1) ||| ((a.p1 ^^^ b.p1) &&& (a.p0 &&& b.p0)))⟩

/-- The planes holding `k` on every lane of the mask `m` and `0` elsewhere. -/
def const (m : ℕ) (k : ZMod 8) : Lanes :=
  ⟨if k.val.testBit 0 then m else 0, if k.val.testBit 1 then m else 0,
    if k.val.testBit 2 then m else 0⟩

/-- Add `k` on every lane of the mask `m`. -/
def addOn (a : Lanes) (m : ℕ) (k : ZMod 8) : Lanes := a.add (const m k)

/-- The residue lane `t` holds. Never evaluated by the kernel. -/
def lane (a : Lanes) (t : ℕ) : ZMod 8 :=
  (if a.p0.testBit t then 1 else 0) + (if a.p1.testBit t then 2 else 0) +
    (if a.p2.testBit t then 4 else 0)

/-- The zero planes hold zero everywhere. -/
@[simp] lemma lane_zero (t : ℕ) : zero.lane t = 0 := by simp [zero, lane]

/-- The adder adds, lane by lane. -/
lemma lane_add (a b : Lanes) (t : ℕ) : (a.add b).lane t = a.lane t + b.lane t := by
  simp only [lane, add, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor]
  cases a.p0.testBit t <;> cases a.p1.testBit t <;> cases a.p2.testBit t <;>
    cases b.p0.testBit t <;> cases b.p1.testBit t <;> cases b.p2.testBit t <;> decide

/-- A bit of a mask that is switched off is off. -/
lemma testBit_ite (c : Bool) (m t : ℕ) : (if c then m else 0).testBit t = (c && m.testBit t) := by
  cases c <;> simp

/-- The constant planes hold `k` on the mask and `0` elsewhere. -/
lemma lane_const (m : ℕ) (k : ZMod 8) (t : ℕ) :
    (const m k).lane t = if m.testBit t then k else 0 := by
  cases hm : m.testBit t <;>
    simp only [lane, const, testBit_ite, hm, Bool.and_false, Bool.and_true] <;> revert k <;> decide

/-- `addOn` adds `k` on the lanes of the mask and nothing elsewhere. -/
lemma lane_addOn (a : Lanes) (m : ℕ) (k : ZMod 8) (t : ℕ) :
    (a.addOn m k).lane t = a.lane t + if m.testBit t then k else 0 := by
  rw [addOn, lane_add, lane_const]

/-- `addOn`, leaving the planes untouched when there is nothing to add: a
zero constant (an `S` or `Z` gate never changes the triple plane) or an
empty mask (a parity of weight below three has no triples). The kernel
allocates a fresh literal even for `x ^^^ 0`, and at 200 wires the triple
plane is 164 KB. Skipping is safe here, and only here: a value every step
reads must be a literal at every step, because the kernel's `whnf` follows
a chain of pass-through terms without consulting its cache, which costs
quadratic time (doing this inside `add`, plane by plane, took the 25-wire
rung of the scale test from 3 s to minutes). The pair and triple planes
are read only by the next gate that changes them, so each chain is
followed once. -/
def addOnz (a : Lanes) (m : ℕ) (k : ZMod 8) : Lanes :=
  if k = 0 then a else if m = 0 then a else a.addOn m k

/-- `addOnz` adds what `addOn` adds. -/
lemma lane_addOnz (a : Lanes) (m : ℕ) (k : ZMod 8) (t : ℕ) :
    (a.addOnz m k).lane t = a.lane t + if m.testBit t then k else 0 := by
  unfold addOnz
  by_cases hk : k = 0
  · simp [hk]
  · by_cases hm : m = 0
    · simp [hk, hm]
    · rw [if_neg hk, if_neg hm]
      exact lane_addOn a m k t

/-- Planes with the same residue in every lane are equal. -/
lemma ext_of_lane {a b : Lanes} (h : ∀ t, a.lane t = b.lane t) : a = b := by
  have key : ∀ t, a.p0.testBit t = b.p0.testBit t ∧ a.p1.testBit t = b.p1.testBit t ∧
      a.p2.testBit t = b.p2.testBit t := by
    intro t
    have := h t
    simp only [lane] at this
    revert this
    cases a.p0.testBit t <;> cases a.p1.testBit t <;> cases a.p2.testBit t <;>
      cases b.p0.testBit t <;> cases b.p1.testBit t <;> cases b.p2.testBit t <;> decide
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  simp only [Lanes.mk.injEq]
  exact ⟨Nat.eq_of_testBit_eq fun t => (key t).1, Nat.eq_of_testBit_eq fun t => (key t).2.1,
    Nat.eq_of_testBit_eq fun t => (key t).2.2⟩

end Lanes

/-! ### The masks of the pairs and triples inside a parity

The lanes of the pairs and triples are numbered in the combinatorial number
system: the pair `(i, j)` with `i < j` has lane `tri j + i`, where
`tri j = C(j, 2)` is the number of pairs below `j`, and the triple
`(i, j, l)` with `i < j < l` has lane `tet l + tri j + i`, where
`tet l = C(l, 3)`. So the pairs with second wire `j` are the lanes
`[tri j, tri (j + 1))`, the triples with third wire `l` are the lanes
`[tet l, tet (l + 1))`, and the planes are exactly `C(n, 2)` and `C(n, 3)`
bits. `pairMask n m` has a bit at the lane of every pair inside `m`: row `j`
is the bits `i < j` of `m` shifted to `tri j`. `tripMask n m` has a bit at
every triple: row `l` is the pairs of `m` below `tri l` shifted to `tet l`.
Both fold one shift-and-or over the set bits of `m` (`maskFold`): for a
dense parity `bitFold`, a loop over the wire indices that touches the
accumulator only at set bits, and for a sparse one `sparseFold`, which
visits only the set bits. The kernel does not accelerate `Nat.log2`, so the
sparse loop finds bits with `gcd` and a population count instead. -/

/-- Fold `g i ||| ·` over the set bits `i < w` of `m`. -/
def bitFold (g : ℕ → ℕ) (m : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | i + 1, acc => bitFold g m i (if m.testBit i then g i ||| acc else acc)

/-- The bits of the fold: those of the start plus those of `g i` for every
set bit `i < w` of `m`. -/
lemma testBit_bitFold (g : ℕ → ℕ) (m w acc t : ℕ) :
    (bitFold g m w acc).testBit t = true ↔
      acc.testBit t = true ∨ ∃ i, i < w ∧ m.testBit i = true ∧ (g i).testBit t = true := by
  induction w generalizing acc with
  | zero => simp [bitFold]
  | succ w ih =>
    simp only [bitFold, ih]
    constructor
    · rintro (h | ⟨i, hi, hm, hg⟩)
      · split at h
        · next hw =>
          rw [Nat.testBit_lor, Bool.or_eq_true] at h
          rcases h with h | h
          · exact Or.inr ⟨w, Nat.lt_succ_self w, hw, h⟩
          · exact Or.inl h
        · exact Or.inl h
      · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hm, hg⟩
    · rintro (h | ⟨i, hi, hm, hg⟩)
      · left
        split
        · rw [Nat.testBit_lor, h, Bool.or_true]
        · exact h
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inr ⟨i, hi, hm, hg⟩
        · left
          rw [if_pos hm, Nat.testBit_lor, hg, Bool.true_or]

/-- `C(j, 2)`, the number of pairs `i < i' < j`; defined by its recurrence
so that the kernel computes it by unfolding. -/
def tri : ℕ → ℕ
  | 0 => 0
  | j + 1 => tri j + j

/-- `C(l, 3)`, the number of triples below `l`, by its recurrence. -/
def tet : ℕ → ℕ
  | 0 => 0
  | l + 1 => tet l + tri l

/-- `tri` is monotone. -/
lemma tri_mono {j j' : ℕ} (h : j ≤ j') : tri j ≤ tri j' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (by simp [tri])

/-- `tet` is monotone. -/
lemma tet_mono {l l' : ℕ} (h : l ≤ l') : tet l ≤ tet l' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (by simp [tet])

/-- The lane of a pair with second wire `j` is below the lanes of the pairs
with second wire `j + 1`. -/
lemma tri_add_lt {i j : ℕ} (h : i < j) : tri j + i < tri (j + 1) := by
  simp only [tri]; omega

/-- The lane of a pair below the lanes of a larger second wire. -/
lemma tri_add_lt_of_lt {i j l : ℕ} (hij : i < j) (hjl : j < l) : tri j + i < tri l :=
  lt_of_lt_of_le (tri_add_lt hij) (tri_mono hjl)

/-- The decomposition `tri j + i` with `i < j` is unique. -/
lemma pair_decomp_unique {i j i' j' : ℕ} (hij : i < j) (hij' : i' < j')
    (h : tri j + i = tri j' + i') : j = j' ∧ i = i' := by
  rcases Nat.lt_trichotomy j j' with hjj | rfl | hjj
  · have := tri_add_lt_of_lt hij hjj
    omega
  · exact ⟨rfl, by omega⟩
  · have := tri_add_lt_of_lt hij' hjj
    omega

/-- The decomposition `tet l + tri j + i` with `i < j < l` is unique. -/
lemma trip_decomp_unique {i j l i' j' l' : ℕ} (hij : i < j) (hjl : j < l) (hij' : i' < j')
    (hjl' : j' < l') (h : tet l + tri j + i = tet l' + tri j' + i') :
    l = l' ∧ j = j' ∧ i = i' := by
  have hl : l = l' := by
    rcases Nat.lt_trichotomy l l' with hll | rfl | hll
    · have h1 := tri_add_lt_of_lt hij hjl
      have h2 : tet (l + 1) ≤ tet l' := tet_mono hll
      simp only [tet] at h2
      omega
    · rfl
    · have h1 := tri_add_lt_of_lt hij' hjl'
      have h2 : tet (l' + 1) ≤ tet l := tet_mono hll
      simp only [tet] at h2
      omega
  subst hl
  obtain ⟨rfl, rfl⟩ := pair_decomp_unique hij hij' (by omega)
  exact ⟨rfl, rfl, rfl⟩

/-- A set bit of a number below `2 ^ n` is below `n`. -/
lemma lt_of_testBit {m j : ℕ} (hm : m < 2 ^ n) (h : m.testBit j = true) : j < n := by
  by_contra hj
  have : m < 2 ^ j := lt_of_lt_of_le hm (Nat.pow_le_pow_right two_pos (not_lt.1 hj))
  rw [Nat.testBit_lt_two_pow this] at h
  exact Bool.false_ne_true h

/-! #### Visiting only the set bits

`bitFold` tests every wire index, so a phase gate on a parity of weight
three on a hundred wires still costs two hundred loop iterations, each a
few dozen kernel steps and some 10 KB of retained terms: the CCZ-network
rungs of the scale test spent 15 ms and 1.9 MB per phase gate on that.
`sparseFold` visits only the set bits, lowest first, with operations the
kernel accelerates: the lowest set bit of `m` is `gcd m (2 ^ W)`, and the
index of a power of two is the population count of its predecessor, by the
usual word-parallel sums on a `W`-bit word. Only the index function needs a
correctness statement, and only on the powers of two below `2 ^ W`, which
is a finite check (`idx_two_pow`). `popCount` also serves, unverified, as
the density heuristic that picks between the two folds (`maskFold`). -/

/-- The word width of the index function; registers of at most this many
wires may use the sparse fold. -/
def idxWidth : ℕ := 1024

/-- The population count of a number below `2 ^ idxWidth`, by word-parallel
sums: fields of two, four, eight and sixteen bits, then one multiplication
that adds every field into the top one. -/
def popCount (x : ℕ) : ℕ :=
  let ones := 2 ^ idxWidth - 1
  let x1 := x - ((x >>> 1) &&& (ones / 3))
  let x2 := (x1 &&& (ones / 5)) + ((x1 >>> 2) &&& (ones / 5))
  let x3 := (x2 + (x2 >>> 4)) &&& (ones / 17)
  let x4 := (x3 + (x3 >>> 8)) &&& (ones / 257)
  ((x4 * (ones / 65535)) >>> (idxWidth - 16)) &&& 65535

/-- The index of a power of two: the population count of its predecessor. -/
def idx (b : ℕ) : ℕ := popCount (b - 1)

/-- `idx` inverts `2 ^ ·` below the word width: a finite check. -/
lemma idx_two_pow : ∀ j, j < idxWidth → idx (2 ^ j) = j := by decide +kernel

/-- The lowest set bit of `m`, as a power of two. -/
def lowBit (m : ℕ) : ℕ := Nat.gcd m (2 ^ idxWidth)

/-- `lowBit` of a non-zero number below `2 ^ idxWidth` is `2 ^ j` for its
lowest set bit `j`. -/
lemma lowBit_spec {m : ℕ} (hm : m ≠ 0) (hlt : m < 2 ^ idxWidth) :
    ∃ j, j < idxWidth ∧ lowBit m = 2 ^ j ∧ m.testBit j = true ∧
      ∀ i, i < j → m.testBit i = false := by
  obtain ⟨j, -, hg⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_right m (2 ^ idxWidth))
  have hdvd : 2 ^ j ∣ m := hg ▸ Nat.gcd_dvd_left m (2 ^ idxWidth)
  obtain ⟨q, rfl⟩ := hdvd
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hjW : j < idxWidth :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1
      (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hq) hlt)
  have hodd : q % 2 = 1 := by
    by_contra hq2
    obtain ⟨r, rfl⟩ : 2 ∣ q := by omega
    have h1 : 2 ^ (j + 1) ∣ 2 ^ j * (2 * r) := ⟨r, by ring⟩
    have h2 : 2 ^ (j + 1) ∣ 2 ^ idxWidth := Nat.pow_dvd_pow 2 hjW
    have h3 : 2 ^ (j + 1) ∣ 2 ^ j := hg ▸ Nat.dvd_gcd h1 h2
    have h4 := Nat.le_of_dvd (Nat.two_pow_pos j) h3
    have h5 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)
    omega
  refine ⟨j, hjW, hg, ?_, fun i hi => ?_⟩
  · rw [Nat.mul_comm, Nat.testBit_mul_two_pow]
    simp [Nat.testBit_zero, hodd]
  · rw [Nat.mul_comm, Nat.testBit_mul_two_pow]
    simp [Nat.not_le.2 hi]

/-- Fold `g i ||| ·` over the set bits of `m`, lowest first, in at most
`fuel` steps. -/
def sparseFold (g : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, m, acc =>
    if m = 0 then acc else sparseFold g fuel (m ^^^ lowBit m) (g (idx (lowBit m)) ||| acc)

/-- The bits of the sparse fold, when the set bits of `m` lie in `[lo, n)`,
the fuel covers that range and `n` fits the index word: those of the start
plus those of `g i` for every set bit `i` of `m`. -/
lemma testBit_sparseFold (g : ℕ → ℕ) (hn : n ≤ idxWidth) (t : ℕ) :
    ∀ (fuel lo m acc : ℕ), (∀ i, m.testBit i = true → lo ≤ i ∧ i < n) → n ≤ lo + fuel →
      ((sparseFold g fuel m acc).testBit t = true ↔
        acc.testBit t = true ∨ ∃ i, m.testBit i = true ∧ (g i).testBit t = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo m acc hbits hfuel
    have hnone : ∀ i, m.testBit i = true → False := fun i hi => by
      have := hbits i hi
      omega
    simp only [sparseFold]
    exact ⟨Or.inl, fun h => h.elim id fun ⟨i, hi, _⟩ => (hnone i hi).elim⟩
  | succ fuel ih =>
    intro lo m acc hbits hfuel
    simp only [sparseFold]
    split
    · next h0 => subst h0; simp
    · next h0 =>
      have hlt : m < 2 ^ idxWidth := Nat.lt_pow_two_of_testBit m fun i hi => by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have := (hbits i hc).2
        omega
      obtain ⟨j, hjW, hb, hmj, hlow⟩ := lowBit_spec h0 hlt
      have hlo : lo ≤ j := (hbits j hmj).1
      rw [hb, idx_two_pow j hjW]
      have hbits' : ∀ i, (m ^^^ 2 ^ j).testBit i = true → j + 1 ≤ i ∧ i < n := by
        intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow] at hi
        rcases eq_or_ne j i with rfl | hji
        · simp [hmj] at hi
        · have hmi : m.testBit i = true := by simpa [hji] using hi
          refine ⟨?_, (hbits i hmi).2⟩
          by_contra hc
          have hij : i < j := by omega
          rw [hlow i hij] at hmi
          exact Bool.false_ne_true hmi
      rw [ih (j + 1) (m ^^^ 2 ^ j) (g j ||| acc) hbits' (by omega), Nat.testBit_lor,
        Bool.or_eq_true]
      constructor
      · rintro ((hg | ha) | ⟨i, hi, hg⟩)
        · exact Or.inr ⟨j, hmj, hg⟩
        · exact Or.inl ha
        · refine Or.inr ⟨i, ?_, hg⟩
          rw [Nat.testBit_xor, Nat.testBit_two_pow] at hi
          rcases eq_or_ne j i with rfl | hji
          · exact hmj
          · simpa [hji] using hi
      · rintro (ha | ⟨i, hi, hg⟩)
        · exact Or.inl (Or.inr ha)
        · rcases eq_or_ne j i with rfl | hji
          · exact Or.inl (Or.inl hg)
          · refine Or.inr ⟨i, ?_, hg⟩
            rw [Nat.testBit_xor, Nat.testBit_two_pow]
            simpa [hji] using hi

/-- Whether to visit set bits rather than test every index: the register
fits the index word and the parity is sparse. The population count is a
heuristic here and needs no proof. -/
def useSparse (n m : ℕ) : Bool := decide (n ≤ idxWidth) && decide (5 * popCount m ≤ n)

/-- Fold `g i ||| ·` over the set bits of a parity `m < 2 ^ n`, by whichever
loop is cheaper. -/
def maskFold (g : ℕ → ℕ) (n m : ℕ) : ℕ :=
  if useSparse n m then sparseFold g n m 0 else bitFold g m n 0

/-- The bits of `maskFold`: those of `g i` for every set bit `i` of `m`. -/
lemma testBit_maskFold (g : ℕ → ℕ) {m : ℕ} (hm : m < 2 ^ n) (t : ℕ) :
    (maskFold g n m).testBit t = true ↔ ∃ i, m.testBit i = true ∧ (g i).testBit t = true := by
  unfold maskFold
  split
  · next hs =>
    have hn : n ≤ idxWidth := by
      simp only [useSparse, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact hs.1
    rw [testBit_sparseFold g hn t n 0 m 0
      (fun i hi => ⟨Nat.zero_le i, lt_of_testBit hm hi⟩) (by omega)]
    simp
  · rw [testBit_bitFold]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    exact ⟨fun ⟨i, _, hi, hg⟩ => ⟨i, hi, hg⟩, fun ⟨i, hi, hg⟩ => ⟨i, lt_of_testBit hm hi, hi, hg⟩⟩

/-- Row `j` of the pair mask: the bits `i < j` of `m`, at the lanes `tri j + i`. -/
def pairRow (m j : ℕ) : ℕ := (m &&& (2 ^ j - 1)) <<< tri j

/-- The pair mask of a parity `m < 2 ^ n`: bit `tri j + i` is set iff `i < j`
are both in `m`. -/
def pairMask (n m : ℕ) : ℕ := maskFold (pairRow m) n m

/-- Row `l` of the triple mask, from the pair mask `p`: the pairs below
`tri l`, which are those with second wire below `l`, at the lanes
`tet l + tri j + i`. -/
def tripRow (p l : ℕ) : ℕ := (p &&& (2 ^ tri l - 1)) <<< tet l

/-- The triple mask of a parity `m < 2 ^ n`: bit `tet l + tri j + i` is set
iff `i < j < l` are all in `m`. -/
def tripMask (n m : ℕ) : ℕ := maskFold (tripRow (pairMask n m)) n m

/-- The bits of a shifted low segment. -/
lemma testBit_land_shiftLeft (x b s t : ℕ) :
    ((x &&& (2 ^ b - 1)) <<< s).testBit t =
      (decide (s ≤ t) && decide (t - s < b) && x.testBit (t - s)) := by
  simp only [Nat.testBit_shiftLeft, Nat.testBit_land, Nat.testBit_two_pow_sub_one, ge_iff_le]
  cases decide (s ≤ t) <;> cases decide (t - s < b) <;> cases x.testBit (t - s) <;> rfl

/-- The bits of a row of the pair mask. -/
lemma testBit_pairRow (m j t : ℕ) :
    (pairRow m j).testBit t =
      (decide (tri j ≤ t) && decide (t - tri j < j) && m.testBit (t - tri j)) :=
  testBit_land_shiftLeft m j (tri j) t

/-- The bits of the pair mask of `m < 2 ^ n`: exactly the lanes of the pairs
inside `m`. -/
lemma testBit_pairMask_iff {m : ℕ} (hm : m < 2 ^ n) (t : ℕ) :
    (pairMask n m).testBit t = true ↔
      ∃ i j, i < j ∧ t = tri j + i ∧ m.testBit i = true ∧ m.testBit j = true := by
  rw [pairMask, testBit_maskFold _ hm]
  simp only [testBit_pairRow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, ⟨ht, hlt⟩, hi⟩
    exact ⟨t - tri j, j, hlt, by omega, hi, hj⟩
  · rintro ⟨i, j, hij, rfl, hi, hj⟩
    refine ⟨j, hj, ⟨by omega, by omega⟩, ?_⟩
    rw [show tri j + i - tri j = i by omega]
    exact hi

/-- Bit `tri j + i` of the pair mask, for `i < j`. -/
lemma testBit_pairMask {m : ℕ} (hm : m < 2 ^ n) {i j : ℕ} (hij : i < j) :
    (pairMask n m).testBit (tri j + i) = (m.testBit i && m.testBit j) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, testBit_pairMask_iff hm]
  constructor
  · rintro ⟨i', j', hij', heq, hi', hj'⟩
    obtain ⟨rfl, rfl⟩ := pair_decomp_unique hij hij' heq
    exact ⟨hi', hj'⟩
  · rintro ⟨hi, hj⟩
    exact ⟨i, j, hij, rfl, hi, hj⟩

/-- A set bit of the pair mask is the lane of a pair below `n`. -/
lemma pairMask_lane {m : ℕ} (hm : m < 2 ^ n) {t : ℕ} (h : (pairMask n m).testBit t = true) :
    ∃ i j, i < j ∧ j < n ∧ t = tri j + i := by
  rw [testBit_pairMask_iff hm] at h
  obtain ⟨i, j, hij, rfl, -, hj⟩ := h
  exact ⟨i, j, hij, lt_of_testBit hm hj, rfl⟩

/-- The bits of a row of the triple mask. -/
lemma testBit_tripRow (p l t : ℕ) :
    (tripRow p l).testBit t =
      (decide (tet l ≤ t) && decide (t - tet l < tri l) && p.testBit (t - tet l)) :=
  testBit_land_shiftLeft p (tri l) (tet l) t

/-- The bits of the triple mask of `m < 2 ^ n`: exactly the lanes of the
triples inside `m`. -/
lemma testBit_tripMask_iff {m : ℕ} (hm : m < 2 ^ n) (t : ℕ) :
    (tripMask n m).testBit t = true ↔
      ∃ i j l, i < j ∧ j < l ∧ t = tet l + tri j + i ∧
        m.testBit i = true ∧ m.testBit j = true ∧ m.testBit l = true := by
  rw [tripMask, testBit_maskFold _ hm]
  simp only [testBit_tripRow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨l, hl, ⟨ht, hlt⟩, hp⟩
    rw [testBit_pairMask_iff hm] at hp
    obtain ⟨i, j, hij, heq, hi, hj⟩ := hp
    have hjl : j < l := by
      by_contra hc
      have := tri_mono (not_lt.1 hc)
      omega
    exact ⟨i, j, l, hij, hjl, by omega, hi, hj, hl⟩
  · rintro ⟨i, j, l, hij, hjl, rfl, hi, hj, hl⟩
    have hlt := tri_add_lt_of_lt hij hjl
    refine ⟨l, hl, ⟨by omega, by omega⟩, ?_⟩
    rw [show tet l + tri j + i - tet l = tri j + i by omega, testBit_pairMask_iff hm]
    exact ⟨i, j, hij, rfl, hi, hj⟩

/-- Bit `tet l + tri j + i` of the triple mask, for `i < j < l`. -/
lemma testBit_tripMask {m : ℕ} (hm : m < 2 ^ n) {i j l : ℕ} (hij : i < j) (hjl : j < l) :
    (tripMask n m).testBit (tet l + tri j + i) =
      (m.testBit i && m.testBit j && m.testBit l) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, testBit_tripMask_iff hm]
  constructor
  · rintro ⟨i', j', l', hij', hjl', heq, hi', hj', hl'⟩
    obtain ⟨rfl, rfl, rfl⟩ := trip_decomp_unique hij hjl hij' hjl' heq
    exact ⟨⟨hi', hj'⟩, hl'⟩
  · rintro ⟨⟨hi, hj⟩, hl⟩
    exact ⟨i, j, l, hij, hjl, rfl, hi, hj, hl⟩

/-- A set bit of the triple mask is the lane of a triple below `n`. -/
lemma tripMask_lane {m : ℕ} (hm : m < 2 ^ n) {t : ℕ} (h : (tripMask n m).testBit t = true) :
    ∃ i j l, i < j ∧ j < l ∧ l < n ∧ t = tet l + tri j + i := by
  rw [testBit_tripMask_iff hm] at h
  obtain ⟨i, j, l, hij, hjl, rfl, -, -, hl⟩ := h
  exact ⟨i, j, l, hij, hjl, lt_of_testBit hm hl, rfl⟩

/-! ### The form -/

/-- The phase-polynomial canonical form of a CNOT-plus-diagonal circuit. -/
@[ext] structure PhasePoly where
  /-- The linear part, packed: bits `n·i .. n·i + n − 1` are row `i`, the
  bitmask of input wires whose parity wire `i` holds (`row`). -/
  rows : ℕ
  /-- The coefficients of the monomials `yᵢ`, in lane `i`. -/
  deg1 : Lanes
  /-- The coefficients of the monomials `yᵢ yⱼ` (`i < j`), in lane `tri j + i`. -/
  deg2 : Lanes
  /-- The coefficients of the monomials `yᵢ yⱼ yₗ` (`i < j < l`), in lane
  `tet l + tri j + i`. -/
  deg3 : Lanes
  deriving DecidableEq, Repr

namespace PhasePoly

/-! #### The normaliser (kernel side) -/

/-- Row `i` of the packed rows: the `n` bits from position `n·i`. -/
def row (n R i : ℕ) : ℕ := (R >>> (n * i)) &&& (2 ^ n - 1)

/-- The rows `i < w` of the identity linear part: row `i` is `2 ^ i`. -/
def initRowsAux (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => initRowsAux n i ||| 2 ^ (n * i + i)

/-- The identity linear part on `n` wires: wire `i` holds input `i`. -/
def initRows (n : ℕ) : ℕ := initRowsAux n n

/-- The form of the empty circuit. -/
def init (n : ℕ) : PhasePoly := ⟨initRows n, .zero, .zero, .zero⟩

/-- The row update of a CNOT: row `t` gains row `c`, one shift and one xor. -/
def cnotRows (n R c t : ℕ) : ℕ := R ^^^ (row n R c <<< (n * t))

/-- Apply a CNOT with control `c` and target `t`. -/
def cnot (n : ℕ) (p : PhasePoly) (c t : ℕ) : PhasePoly :=
  { p with rows := cnotRows n p.rows c t }

/-- Apply a diagonal gate of phase `k` on wire `i`: add `k · (m · y)` for the
parity `m` of wire `i`, as `k` on each wire of `m`, `−2k` on each pair and
`4k` on each triple. -/
def diag (n : ℕ) (p : PhasePoly) (i : ℕ) (k : ZMod 8) : PhasePoly :=
  let m := row n p.rows i
  { p with
    deg1 := p.deg1.addOn m k
    deg2 := p.deg2.addOnz (pairMask n m) (6 * k)
    deg3 := p.deg3.addOnz (tripMask n m) (4 * k) }

/-- One instruction; `none` outside the fragment. A CNOT whose control is
its target is rejected: it is not a permutation of the basis. -/
def step (p : PhasePoly) : Instr n → Option PhasePoly
  | .cnot c t => if c = t then none else some (p.cnot n c.val t.val)
  | .one g i =>
    match g.phase? with
    | some k => some (p.diag n i.val k)
    | none => none

/-- Run the normaliser over a circuit from the form `p`. -/
def run : Circuit n → PhasePoly → Option PhasePoly
  | [], p => some p
  | g :: c, p =>
    match p.step g with
    | some p' => run c p'
    | none => none

/-- The normal form of a circuit; `none` outside the fragment. -/
def nf (c : Circuit n) : Option PhasePoly := run c (init n)

/-! #### The linear part (proof side) -/

/-- The parity of the bits of `m` below position `w`: `true` iff an odd
number of them are set. Never evaluated by the kernel; the bound `w` keeps
the definition structural. -/
def parityBelow : ℕ → ℕ → Bool
  | 0, _ => false
  | w + 1, m => (m.testBit w ^^ parityBelow w m)

/-- `0` has even parity. -/
@[simp] lemma parityBelow_zero (w : ℕ) : parityBelow w 0 = false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [parityBelow, ih]

/-- Parity is additive under `xor`. -/
lemma parityBelow_xor (w a b : ℕ) :
    parityBelow w (a ^^^ b) = (parityBelow w a ^^ parityBelow w b) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [parityBelow, Nat.testBit_xor, ih]
    generalize a.testBit w = p
    generalize b.testBit w = q
    generalize parityBelow w a = r
    generalize parityBelow w b = s
    revert p q r s
    decide

/-- A single bit at or above the bound contributes nothing. -/
lemma parityBelow_two_pow_land_of_le {w i : ℕ} (h : w ≤ i) (y : ℕ) :
    parityBelow w (2 ^ i &&& y) = false := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have hne : i ≠ w := by omega
    simp [parityBelow, hne, ih (by omega)]

/-- The parity of a single input bit. -/
lemma parityBelow_two_pow_land {w i : ℕ} (h : i < w) (y : ℕ) :
    parityBelow w (2 ^ i &&& y) = y.testBit i := by
  induction w with
  | zero => omega
  | succ w ih =>
    rcases Nat.lt_or_ge i w with h' | h'
    · have hne : i ≠ w := by omega
      simp [parityBelow, hne, ih h']
    · have hiw : i = w := by omega
      subst hiw
      simp [parityBelow, parityBelow_two_pow_land_of_le (le_refl i)]

/-- The bits of a row. -/
lemma testBit_row (n R i b : ℕ) :
    (row n R i).testBit b = (decide (b < n) && R.testBit (n * i + b)) := by
  simp only [row, Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  exact Bool.and_comm _ _

/-- A row is a mask of the `n` inputs. -/
lemma row_lt (n R i : ℕ) : row n R i < 2 ^ n := by
  rw [row, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

/-- The decomposition `n·i + b` with `b < n` is unique. -/
lemma row_decomp_unique {i b i' b' : ℕ} (hb : b < n) (hb' : b' < n)
    (h : n * i + b = n * i' + b') : i = i' ∧ b = b' := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le b) hb
  have h1 : (n * i + b) / n = i := by rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hb, add_zero]
  have h2 : (n * i' + b') / n = i' := by rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hb', add_zero]
  have hi : i = i' := by rw [← h1, h, h2]
  subst hi
  exact ⟨rfl, by omega⟩

/-- The bits of a shifted row land in row `t` only. -/
lemma testBit_row_shiftLeft {v : ℕ} (hv : v < 2 ^ n) (t i b : ℕ) (hb : b < n) :
    (v <<< (n * t)).testBit (n * i + b) = (decide (i = t) && v.testBit b) := by
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy i t with hit | rfl | hit
  · have h1 : n * (i + 1) ≤ n * t := Nat.mul_le_mul_left n hit
    have h2 : n * (i + 1) = n * i + n := Nat.mul_succ n i
    have : ¬ (n * i + b ≥ n * t) := by omega
    simp [this, ne_of_lt hit]
  · simp [show n * i + b - n * i = b by omega]
  · have h1 : n * (t + 1) ≤ n * i := Nat.mul_le_mul_left n hit
    have h2 : n * (t + 1) = n * t + n := Nat.mul_succ n t
    have h3 : n * i + b - n * t ≥ n := by omega
    have h4 : v.testBit (n * i + b - n * t) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right two_pos h3))
    simp [h4, ne_of_gt hit]

/-- The rows after a CNOT: row `t` gains row `c`, the others are unchanged. -/
lemma row_cnotRows (n R c t i : ℕ) :
    row n (cnotRows n R c t) i = if i = t then row n R t ^^^ row n R c else row n R i := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < n
  · rw [testBit_row, cnotRows, Nat.testBit_xor, testBit_row_shiftLeft (row_lt n R c) t i b hb]
    split_ifs with hit
    · subst hit
      simp [Nat.testBit_xor, testBit_row, hb]
    · simp [testBit_row, hb, hit]
  · have h1 : row n (cnotRows n R c t) i < 2 ^ b :=
      lt_of_lt_of_le (row_lt _ _ _) (Nat.pow_le_pow_right two_pos (not_lt.1 hb))
    rw [Nat.testBit_lt_two_pow h1]
    split_ifs
    · rw [Nat.testBit_xor, Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
      · rfl
      all_goals exact lt_of_lt_of_le (row_lt _ _ _) (Nat.pow_le_pow_right two_pos (not_lt.1 hb))
    · exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (row_lt _ _ _) (Nat.pow_le_pow_right two_pos (not_lt.1 hb)))).symm

/-- The bits of the identity rows: exactly the positions `n·i + i` for `i < w`. -/
lemma testBit_initRowsAux (n w x : ℕ) :
    (initRowsAux n w).testBit x = true ↔ ∃ i, i < w ∧ x = n * i + i := by
  induction w with
  | zero => simp [initRowsAux]
  | succ w ih =>
    simp only [initRowsAux, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.testBit_two_pow,
      decide_eq_true_eq]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
      · exact ⟨w, Nat.lt_succ_self w, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr rfl

/-- Row `i` of the identity rows is the single bit `i`. -/
lemma row_initRows {i : ℕ} (h : i < n) : row n (initRows n) i = 2 ^ i := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_row, Nat.testBit_two_pow]
  by_cases hb : b < n
  · simp only [hb, decide_true, Bool.true_and]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, initRows, testBit_initRowsAux]
    constructor
    · rintro ⟨i', hi', heq⟩
      obtain ⟨h1, h2⟩ := row_decomp_unique hb hi' heq
      exact h1.trans h2.symm
    · rintro rfl
      exact ⟨i, h, rfl⟩
  · have : i ≠ b := fun e => hb (e ▸ h)
    simp [hb, this]

/-- The output index of the linear part on input `y`, built bit by bit:
bit `i < w` is the parity of `row i &&& y`. -/
def linNatAux (n R y : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => linNatAux n R y i ||| (if parityBelow n (row n R i &&& y) then 2 ^ i else 0)

/-- Bit `i` of `linNatAux` is the parity of `row i &&& y`, for `i < w`. -/
lemma testBit_linNatAux (n R y w i : ℕ) :
    (linNatAux n R y w).testBit i = (decide (i < w) && parityBelow n (row n R i &&& y)) := by
  induction w with
  | zero => simp [linNatAux]
  | succ w ih =>
    simp only [linNatAux, Nat.testBit_lor, ih, Lanes.testBit_ite, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i w with hiw | rfl | hiw
    · simp [hiw, Nat.lt_succ_of_lt hiw, ne_of_gt hiw]
    · simp
    · have h1 : ¬ i < w := by omega
      have h2 : ¬ i < w + 1 := by omega
      simp [h1, h2, ne_of_lt hiw]

/-- The output basis index of the linear part on input `y`. -/
def linFin (R : ℕ) (y : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨linNatAux n R y.val n % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- Bit `i` of the output index is the parity of `row i &&& y`. -/
lemma bit_linFin (R : ℕ) (y : Fin (2 ^ n)) (i : Fin n) :
    bit i (linFin R y) = parityBelow n (row n R i.val &&& y.val) := by
  simp [bit, linFin, Nat.testBit_mod_two_pow, i.isLt, testBit_linNatAux]

/-- The row update of a CNOT is the CNOT's action on the output index. -/
lemma linFin_cnotRows (R : ℕ) {c t : Fin n} (hct : c ≠ t) (y : Fin (2 ^ n)) :
    linFin (cnotRows n R c.val t.val) y =
      if bit c (linFin R y) then flipBit t (linFin R y) else linFin R y := by
  apply eq_of_bit_eq
  intro j
  rw [bit_linFin, row_cnotRows]
  by_cases hjt : j = t
  · subst hjt
    rw [if_pos rfl, Nat.and_xor_distrib_right, parityBelow_xor, ← bit_linFin, ← bit_linFin]
    cases bit c (linFin R y) <;> simp
  · have hjt' : j.val ≠ t.val := fun e => hjt (Fin.ext e)
    rw [if_neg hjt', ← bit_linFin]
    cases bit c (linFin R y) <;> simp [bit_flipBit_of_ne hjt]

/-- The identity rows give the identity map. -/
lemma linFin_initRows (y : Fin (2 ^ n)) : linFin (initRows n) y = y :=
  eq_of_bit_eq fun i => by
    rw [bit_linFin, row_initRows i.isLt, parityBelow_two_pow_land i.isLt]; rfl

/-! #### The phase polynomial (proof side)

The polynomial is evaluated as sums over `Finset.range` in `ZMod 8`, with
`ind y i` the bit `i` of `y` as a residue; the inner sums over `range j`
put the pairs and triples in increasing order, matching the lanes. -/

/-- Bit `i` of `y`, as a residue. -/
def ind (y i : ℕ) : ZMod 8 := if y.testBit i then 1 else 0

/-- The parity of `z` below `w`, as a residue. -/
def parityInd (w z : ℕ) : ZMod 8 := if parityBelow w z then 1 else 0

/-- The degree-one part of the polynomial at `y`. -/
def eval1 (n : ℕ) (a : Lanes) (y : ℕ) : ZMod 8 := ∑ i ∈ range n, ind y i * a.lane i

/-- The degree-two part of the polynomial at `y`. -/
def eval2 (n : ℕ) (a : Lanes) (y : ℕ) : ZMod 8 :=
  ∑ j ∈ range n, ∑ i ∈ range j, ind y i * ind y j * a.lane (tri j + i)

/-- The degree-three part of the polynomial at `y`. -/
def eval3 (n : ℕ) (a : Lanes) (y : ℕ) : ZMod 8 :=
  ∑ l ∈ range n, ∑ j ∈ range l, ∑ i ∈ range j,
    ind y i * ind y j * ind y l * a.lane (tet l + tri j + i)

/-- The polynomial of a form at the input `y`. -/
def phaseAt (n : ℕ) (P : PhasePoly) (y : ℕ) : ZMod 8 :=
  eval1 n P.deg1 y + eval2 n P.deg2 y + eval3 n P.deg3 y

/-- The set bits of `z` below `w`, counted as a residue. -/
def cnt1 (w z : ℕ) : ZMod 8 := ∑ i ∈ range w, ind z i

/-- The pairs of set bits of `z` below `w`, counted as a residue. -/
def cnt2 (w z : ℕ) : ZMod 8 := ∑ j ∈ range w, ∑ i ∈ range j, ind z i * ind z j

/-- The triples of set bits of `z` below `w`, counted as a residue. -/
def cnt3 (w z : ℕ) : ZMod 8 :=
  ∑ l ∈ range w, ∑ j ∈ range l, ∑ i ∈ range j, ind z i * ind z j * ind z l

/-- The indicator of an intersection is the product of the indicators. -/
lemma ind_land (m y i : ℕ) : ind (m &&& y) i = ind m i * ind y i := by
  simp only [ind, Nat.testBit_land]
  cases m.testBit i <;> cases y.testBit i <;> simp

/-- Adding `k` on the wires of `m` adds `k` times the count of `m ∩ y`. -/
lemma eval1_addOn (n : ℕ) (a : Lanes) (m : ℕ) (k : ZMod 8) (y : ℕ) :
    eval1 n (a.addOn m k) y = eval1 n a y + k * cnt1 n (m &&& y) := by
  simp only [eval1, cnt1, Lanes.lane_addOn, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    ind_land]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ind]
  cases m.testBit i <;> cases y.testBit i <;> simp

/-- Adding `k` on the pairs of `m` adds `k` times the pair count of `m ∩ y`. -/
lemma eval2_addOn (a : Lanes) {m : ℕ} (hm : m < 2 ^ n) (k : ZMod 8) (y : ℕ) :
    eval2 n (a.addOnz (pairMask n m) k) y = eval2 n a y + k * cnt2 n (m &&& y) := by
  simp only [eval2, cnt2, Lanes.lane_addOnz, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    ind_land]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [testBit_pairMask hm hi]
  simp only [ind]
  cases m.testBit i <;> cases m.testBit j <;> cases y.testBit i <;> cases y.testBit j <;> simp

/-- Adding `k` on the triples of `m` adds `k` times the triple count of
`m ∩ y`. -/
lemma eval3_addOn (a : Lanes) {m : ℕ} (hm : m < 2 ^ n) (k : ZMod 8) (y : ℕ) :
    eval3 n (a.addOnz (tripMask n m) k) y = eval3 n a y + k * cnt3 n (m &&& y) := by
  simp only [eval3, cnt3, Lanes.lane_addOnz, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    ind_land]
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi hj
  rw [testBit_tripMask hm hi hj]
  simp only [ind]
  cases m.testBit i <;> cases m.testBit j <;> cases m.testBit l <;> cases y.testBit i <;>
    cases y.testBit j <;> cases y.testBit l <;> simp

/-- One more wire adds its bit to the count. -/
lemma cnt1_succ (w z : ℕ) : cnt1 (w + 1) z = cnt1 w z + ind z w := Finset.sum_range_succ _ _

/-- One more wire pairs with every earlier set bit. -/
lemma cnt2_succ (w z : ℕ) : cnt2 (w + 1) z = cnt2 w z + ind z w * cnt1 w z := by
  rw [cnt2, Finset.sum_range_succ, ← cnt2, cnt1, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- One more wire completes a triple with every earlier pair. -/
lemma cnt3_succ (w z : ℕ) : cnt3 (w + 1) z = cnt3 w z + ind z w * cnt2 w z := by
  rw [cnt3, Finset.sum_range_succ, ← cnt3, cnt2, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `xor` as a polynomial on residues that are `0` or `1`. -/
lemma ite_xor (b p : Bool) :
    (if (b ^^ p) = true then (1 : ZMod 8) else 0) =
      (if p = true then 1 else 0) + (if b = true then 1 else 0) -
        2 * (if b = true then 1 else 0) * (if p = true then 1 else 0) := by
  cases b <;> cases p <;> decide

/-- One more wire flips the parity when its bit is set. -/
lemma parityInd_succ (w z : ℕ) :
    parityInd (w + 1) z = parityInd w z + ind z w - 2 * ind z w * parityInd w z := by
  simp only [parityInd, parityBelow, ind]
  exact ite_xor _ _

/-- The count identity: `s − 2·C(s,2) + 4·C(s,3) ≡ s mod 2 (mod 8)`, wire by
wire. -/
lemma cnt_parity (w z : ℕ) : cnt1 w z - 2 * cnt2 w z + 4 * cnt3 w z = parityInd w z := by
  induction w with
  | zero => simp [cnt1, cnt2, cnt3, parityInd, parityBelow]
  | succ w ih =>
    rw [cnt1_succ, cnt2_succ, cnt3_succ, parityInd_succ, ← ih]
    have h8 : (8 : ZMod 8) = 0 := by decide
    linear_combination (ind z w * cnt3 w z) * h8

/-- A diagonal gate adds `k · (m · y)` to the polynomial. -/
lemma phaseAt_diag (n : ℕ) (P : PhasePoly) (i : ℕ) (k : ZMod 8) (y : ℕ) :
    phaseAt n (P.diag n i k) y = phaseAt n P y + k * parityInd n (row n P.rows i &&& y) := by
  have h8 : (8 : ZMod 8) = 0 := by decide
  simp only [phaseAt, diag, eval1_addOn, eval2_addOn _ (row_lt n P.rows i),
    eval3_addOn _ (row_lt n P.rows i), ← cnt_parity]
  linear_combination (k * cnt2 n (row n P.rows i &&& y)) * h8

/-- The action of a form on a basis vector: a phase times a basis vector. -/
def act (P : PhasePoly) (y : Fin (2 ^ n)) : Vec n :=
  ωpow (phaseAt n P y.val) • basis (linFin P.rows y)

/-- The form of the empty circuit acts as the identity. -/
lemma act_init (y : Fin (2 ^ n)) : (init n).act y = basis y := by
  simp [act, init, linFin_initRows, phaseAt, eval1, eval2, eval3]

/-! #### Soundness -/

/-- A diagonal gate keeps the rows. -/
@[simp] lemma rows_diag (P : PhasePoly) (i : ℕ) (k : ZMod 8) : (P.diag n i k).rows = P.rows := rfl

/-- One step of the normaliser tracks the instruction's action. -/
lemma apply_act {P P' : PhasePoly} {g : Instr n} (h : P.step g = some P') (y : Fin (2 ^ n)) :
    g.apply (P.act y) = P'.act y := by
  cases g with
  | cnot c t =>
    by_cases hct : c = t
    · simp [step, hct] at h
    · simp only [step, hct, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [act, Instr.apply_cnot, applyCNOT_smul, applyCNOT_basis hct, cnot,
        linFin_cnotRows _ hct, phaseAt]
  | one g i =>
    cases hg : g.phase? with
    | none => simp [step, hg] at h
    | some k =>
      simp only [step, hg, Option.some.injEq] at h
      subst h
      have hoff := Gate1.mat_off_diag_of_isDiag (Gate1.isDiag_of_phase? hg)
      simp only [act, Instr.apply_one, applyOne_smul, applyOne_basis_of_diag hoff,
        Gate1.mat_diag_of_phase? hg, rows_diag, phaseAt_diag, ωpow_add, bit_linFin,
        smul_smul, parityInd, mul_ite, mul_one, mul_zero]

/-- The normaliser tracks the denotation from any starting form. -/
theorem run_sound {c : Circuit n} {P Q : PhasePoly} (h : run c P = some Q) (y : Fin (2 ^ n)) :
    denote c (P.act y) = Q.act y := by
  induction c generalizing P with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    rfl
  | cons g c ih =>
    simp only [run] at h
    cases hs : P.step g with
    | none => simp [hs] at h
    | some P' =>
      simp only [hs] at h
      rw [denote_cons, apply_act hs, ih h]

/-- A normal form describes the circuit's action on every basis vector. -/
theorem nf_sound {c : Circuit n} {P : PhasePoly} (h : nf c = some P) (y : Fin (2 ^ n)) :
    denote c (basis y) = P.act y := by
  rw [← act_init y]
  exact run_sound h y

/-- Equal normal forms are equivalent circuits. -/
theorem sound {a b : Circuit n} {P : PhasePoly} (ha : nf a = some P) (hb : nf b = some P) :
    a ≡ᵤ b :=
  (equivalent_iff_basis a b).2 fun y => (nf_sound ha y).trans (nf_sound hb y).symm


/-! #### Completeness

Equal unitaries give equal forms. The action on `|y⟩` determines the
output index and the phase (`act_inj`); the output indices at the unit
vectors determine the rows; the phases at the inputs of weight one, two
and three determine the coefficients degree by degree (`phaseAt_two_pow`,
`phaseAt_two_pow_two`, `phaseAt_two_pow_three`); and the invariant `WF`,
kept by every step, says every other lane and every other bit of the rows
is zero, so equal coefficients are equal planes (`ext_of_agree`). -/

/-- The lanes and row bits a form on `n` wires may use: rows below `2 ^ n²`
and only the lanes of monomials on `n` wires. Every normal form satisfies
it (`wf_nf`). -/
def WF (n : ℕ) (P : PhasePoly) : Prop :=
  P.rows < 2 ^ (n * n) ∧
  (∀ t, n ≤ t → P.deg1.lane t = 0) ∧
  (∀ t, (∀ i j, i < j → j < n → t ≠ tri j + i) → P.deg2.lane t = 0) ∧
  (∀ t, (∀ i j l, i < j → j < l → l < n → t ≠ tet l + tri j + i) → P.deg3.lane t = 0)

/-- The identity rows are below `2 ^ n²`. -/
lemma initRows_lt (n : ℕ) : initRows n < 2 ^ (n * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro x hx
  by_contra h
  rw [Bool.not_eq_false, initRows, testBit_initRowsAux] at h
  obtain ⟨i, hi, rfl⟩ := h
  have h1 : n * (i + 1) ≤ n * n := Nat.mul_le_mul_left n hi
  have h2 : n * (i + 1) = n * i + n := Nat.mul_succ n i
  omega

/-- A CNOT onto a wire below `n` keeps the rows below `2 ^ n²`. -/
lemma cnotRows_lt {R : ℕ} (hR : R < 2 ^ (n * n)) (c : ℕ) {t : ℕ} (ht : t < n) :
    cnotRows n R c t < 2 ^ (n * n) := by
  apply Nat.xor_lt_two_pow hR
  have h1 : row n R c <<< (n * t) < 2 ^ (n + n * t) := Nat.shiftLeft_lt (row_lt n R c)
  refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right two_pos ?_)
  have h2 : n * (t + 1) ≤ n * n := Nat.mul_le_mul_left n ht
  have h3 : n * (t + 1) = n * t + n := Nat.mul_succ n t
  omega

/-- The initial form is well-formed. -/
lemma wf_init (n : ℕ) : WF n (init n) :=
  ⟨initRows_lt n, fun _ _ => Lanes.lane_zero _, fun _ _ => Lanes.lane_zero _,
    fun _ _ => Lanes.lane_zero _⟩

/-- A step keeps well-formedness: the masks of a diagonal gate name only
lanes of monomials. -/
lemma wf_step {P P' : PhasePoly} (hP : WF n P) {g : Instr n} (h : P.step g = some P') :
    WF n P' := by
  obtain ⟨hr, h1, h2, h3⟩ := hP
  cases g with
  | cnot c t =>
    by_cases hct : c = t
    · simp [step, hct] at h
    · simp only [step, hct, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨cnotRows_lt hr c.val t.isLt, h1, h2, h3⟩
  | one g i =>
    cases hg : g.phase? with
    | none => simp [step, hg] at h
    | some k =>
      simp only [step, hg, Option.some.injEq] at h
      subst h
      have hm := row_lt n P.rows i.val
      refine ⟨hr, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
      · change (P.deg1.addOn (row n P.rows i.val) k).lane t = 0
        rw [Lanes.lane_addOn, h1 t ht,
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right two_pos ht))]
        simp
      · change (P.deg2.addOnz (pairMask n (row n P.rows i.val)) (6 * k)).lane t = 0
        rw [Lanes.lane_addOnz, h2 t ht]
        have hf : (pairMask n (row n P.rows i.val)).testBit t = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          obtain ⟨i', j', hij, hjn, rfl⟩ := pairMask_lane hm hc
          exact ht i' j' hij hjn rfl
        simp [hf]
      · change (P.deg3.addOnz (tripMask n (row n P.rows i.val)) (4 * k)).lane t = 0
        rw [Lanes.lane_addOnz, h3 t ht]
        have hf : (tripMask n (row n P.rows i.val)).testBit t = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          obtain ⟨i', j', l', hij, hjl, hln, rfl⟩ := tripMask_lane hm hc
          exact ht i' j' l' hij hjl hln rfl
        simp [hf]

/-- The normaliser keeps well-formedness. -/
theorem wf_run {c : Circuit n} {P Q : PhasePoly} (hP : WF n P) (h : run c P = some Q) :
    WF n Q := by
  induction c generalizing P with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact hP
  | cons g c ih =>
    simp only [run] at h
    cases hs : P.step g with
    | none => simp [hs] at h
    | some P' =>
      simp only [hs] at h
      exact ih (wf_step hP hs) h

/-- A normal form is well-formed. -/
theorem wf_nf {c : Circuit n} {P : PhasePoly} (h : nf c = some P) : WF n P :=
  wf_run (wf_init n) h

/-- `∑_{i < w} yᵢ · f i`, the shape of every sum in the polynomial. -/
def sum1 (w : ℕ) (f : ℕ → ZMod 8) (y : ℕ) : ZMod 8 := ∑ i ∈ range w, ind y i * f i

/-- The degree-one part as a `sum1`. -/
lemma eval1_eq_sum1 (n : ℕ) (a : Lanes) (y : ℕ) : eval1 n a y = sum1 n a.lane y := rfl

/-- The degree-two part as nested `sum1`s. -/
lemma eval2_eq_sum1 (n : ℕ) (a : Lanes) (y : ℕ) :
    eval2 n a y = sum1 n (fun j => sum1 j (fun i => a.lane (tri j + i)) y) y := by
  simp only [eval2, sum1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- The degree-three part as nested `sum1`s. -/
lemma eval3_eq_sum1 (n : ℕ) (a : Lanes) (y : ℕ) :
    eval3 n a y =
      sum1 n (fun l => sum1 l (fun j => sum1 j (fun i => a.lane (tet l + tri j + i)) y) y) y := by
  simp only [eval3, sum1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

/-- At a unit vector the sum picks one term. -/
lemma sum1_two_pow (w : ℕ) (f : ℕ → ZMod 8) (i : ℕ) :
    sum1 w f (2 ^ i) = if i < w then f i else 0 := by
  simp [sum1, ind, Nat.testBit_two_pow, ite_mul, Finset.sum_ite_eq, Finset.mem_range]

/-- The indicator of a disjoint union is the sum of the indicators. -/
lemma ind_lor_of_disjoint {a b : ℕ} (h : a &&& b = 0) (i : ℕ) :
    ind (a ||| b) i = ind a i + ind b i := by
  have hab : (a.testBit i && b.testBit i) = false := by
    rw [← Nat.testBit_land, h, Nat.zero_testBit]
  simp only [ind, Nat.testBit_lor]
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

/-- The sum over a disjoint union of inputs is the sum of the sums. -/
lemma sum1_lor {a b : ℕ} (h : a &&& b = 0) (w : ℕ) (f : ℕ → ZMod 8) :
    sum1 w f (a ||| b) = sum1 w f a + sum1 w f b := by
  simp only [sum1, ind_lor_of_disjoint h, add_mul, Finset.sum_add_distrib]

/-- Distinct unit vectors are disjoint. -/
lemma two_pow_land_two_pow {i j : ℕ} (h : i ≠ j) : 2 ^ i &&& 2 ^ j = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_land, Nat.zero_testBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
  rcases eq_or_ne i t with rfl | hit
  · simp [Ne.symm h]
  · simp [hit]

/-- A unit vector is disjoint from the union of two others. -/
lemma two_pow_land_lor {i j l : ℕ} (hij : i ≠ j) (hil : i ≠ l) :
    2 ^ i &&& (2 ^ j ||| 2 ^ l) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_land, Nat.testBit_lor, Nat.zero_testBit, Nat.testBit_two_pow,
    Nat.testBit_two_pow, Nat.testBit_two_pow]
  rcases eq_or_ne i t with rfl | hit
  · simp [Ne.symm hij, Ne.symm hil]
  · simp [hit]

/-- The polynomial at the unit vector `eᵢ` is the coefficient of `yᵢ`. -/
lemma phaseAt_two_pow (P : PhasePoly) {i : ℕ} (hi : i < n) :
    phaseAt n P (2 ^ i) = P.deg1.lane i := by
  simp [phaseAt, eval1_eq_sum1, eval2_eq_sum1, eval3_eq_sum1, sum1_two_pow, hi]

/-- The polynomial at `eᵢ + eⱼ` (`i < j`): the two linear coefficients and
the coefficient of `yᵢ yⱼ`. -/
lemma phaseAt_two_pow_two (P : PhasePoly) {i j : ℕ} (hij : i < j) (hj : j < n) :
    phaseAt n P (2 ^ i ||| 2 ^ j) =
      P.deg1.lane i + P.deg1.lane j + P.deg2.lane (tri j + i) := by
  have hd := two_pow_land_two_pow (ne_of_lt hij)
  have hi : i < n := lt_trans hij hj
  have hji : ¬ j < i := by omega
  simp [phaseAt, eval1_eq_sum1, eval2_eq_sum1, eval3_eq_sum1, sum1_lor hd, sum1_two_pow, hi, hj,
    hij, hji]

/-- The polynomial at `eᵢ + eⱼ + eₗ` (`i < j < l`): the three linear
coefficients, the three pair coefficients and the coefficient of
`yᵢ yⱼ yₗ`. -/
lemma phaseAt_two_pow_three (P : PhasePoly) {i j l : ℕ} (hij : i < j) (hjl : j < l)
    (hl : l < n) :
    phaseAt n P (2 ^ i ||| (2 ^ j ||| 2 ^ l)) =
      P.deg1.lane i + P.deg1.lane j + P.deg1.lane l +
        (P.deg2.lane (tri j + i) + P.deg2.lane (tri l + i) + P.deg2.lane (tri l + j)) +
        P.deg3.lane (tet l + tri j + i) := by
  have hd1 := two_pow_land_lor (ne_of_lt hij) (ne_of_lt (lt_trans hij hjl))
  have hd2 := two_pow_land_two_pow (ne_of_lt hjl)
  have hi : i < n := lt_trans hij (lt_trans hjl hl)
  have hj : j < n := lt_trans hjl hl
  have hil : i < l := lt_trans hij hjl
  have hji : ¬ j < i := by omega
  have hli : ¬ l < i := by omega
  have hlj : ¬ l < j := by omega
  simp [phaseAt, eval1_eq_sum1, eval2_eq_sum1, eval3_eq_sum1, sum1_lor hd1, sum1_lor hd2,
    sum1_two_pow, hi, hj, hl, hij, hjl, hil, hji, hli, hlj]
  ring

/-- A bit of the packed rows, read through its row. -/
lemma testBit_eq_row (R i : ℕ) {b : ℕ} (hb : b < n) :
    R.testBit (n * i + b) = (row n R i).testBit b := by
  rw [testBit_row, decide_eq_true hb, Bool.true_and]

/-- Well-formed forms with the same rows on every wire and the same
polynomial on every input are equal. -/
theorem ext_of_agree {P Q : PhasePoly} (hP : WF n P) (hQ : WF n Q)
    (hrows : ∀ i, i < n → row n P.rows i = row n Q.rows i)
    (hφ : ∀ y, y < 2 ^ n → phaseAt n P y = phaseAt n Q y) : P = Q := by
  have e1 : ∀ i, i < n → P.deg1.lane i = Q.deg1.lane i := fun i hi => by
    have h := hφ (2 ^ i) (Nat.pow_lt_pow_right one_lt_two hi)
    rwa [phaseAt_two_pow P hi, phaseAt_two_pow Q hi] at h
  have e2 : ∀ i j, i < j → j < n → P.deg2.lane (tri j + i) = Q.deg2.lane (tri j + i) :=
    fun i j hij hj => by
      have h := hφ (2 ^ i ||| 2 ^ j) (Nat.or_lt_two_pow
        (Nat.pow_lt_pow_right one_lt_two (lt_trans hij hj)) (Nat.pow_lt_pow_right one_lt_two hj))
      rw [phaseAt_two_pow_two P hij hj, phaseAt_two_pow_two Q hij hj, e1 i (lt_trans hij hj),
        e1 j hj] at h
      exact add_left_cancel h
  have e3 : ∀ i j l, i < j → j < l → l < n →
      P.deg3.lane (tet l + tri j + i) = Q.deg3.lane (tet l + tri j + i) :=
    fun i j l hij hjl hl => by
      have hi : i < n := lt_trans hij (lt_trans hjl hl)
      have hj : j < n := lt_trans hjl hl
      have h := hφ (2 ^ i ||| (2 ^ j ||| 2 ^ l)) (Nat.or_lt_two_pow
        (Nat.pow_lt_pow_right one_lt_two hi) (Nat.or_lt_two_pow
          (Nat.pow_lt_pow_right one_lt_two hj) (Nat.pow_lt_pow_right one_lt_two hl)))
      rw [phaseAt_two_pow_three P hij hjl hl, phaseAt_two_pow_three Q hij hjl hl, e1 i hi,
        e1 j hj, e1 l hl, e2 i j hij hj, e2 i l (lt_trans hij hjl) hl, e2 j l hjl hl] at h
      exact add_left_cancel h
  obtain ⟨rP, sP1, sP2, sP3⟩ := hP
  obtain ⟨rQ, sQ1, sQ2, sQ3⟩ := hQ
  refine PhasePoly.ext ?_ ?_ ?_ ?_
  · apply Nat.eq_of_testBit_eq
    intro x
    by_cases hx : x < n * n
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp at hx
        · exact hn
      have hdiv : x / n < n := Nat.div_lt_of_lt_mul hx
      have hmod : x % n < n := Nat.mod_lt x hn
      have hx' : x = n * (x / n) + x % n := (Nat.div_add_mod x n).symm
      rw [hx', testBit_eq_row _ _ hmod, testBit_eq_row _ _ hmod, hrows _ hdiv]
    · have hle : 2 ^ (n * n) ≤ 2 ^ x := Nat.pow_le_pow_right two_pos (not_lt.1 hx)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le rP hle),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le rQ hle)]
  · refine Lanes.ext_of_lane fun t => ?_
    by_cases ht : t < n
    · exact e1 t ht
    · rw [sP1 t (not_lt.1 ht), sQ1 t (not_lt.1 ht)]
  · refine Lanes.ext_of_lane fun t => ?_
    by_cases ht : ∃ i j, i < j ∧ j < n ∧ t = tri j + i
    · obtain ⟨i, j, hij, hj, rfl⟩ := ht
      exact e2 i j hij hj
    · push Not at ht
      rw [sP2 t ht, sQ2 t ht]
  · refine Lanes.ext_of_lane fun t => ?_
    by_cases ht : ∃ i j l, i < j ∧ j < l ∧ l < n ∧ t = tet l + tri j + i
    · obtain ⟨i, j, l, hij, hjl, hl, rfl⟩ := ht
      exact e3 i j l hij hjl hl
    · push Not at ht
      rw [sP3 t ht, sQ3 t ht]

/-- Equal actions on a basis vector give the same output index and the same
phase: the phase is a non-zero scalar and `ω` has order eight. -/
lemma act_inj {P Q : PhasePoly} {y : Fin (2 ^ n)} (h : P.act y = Q.act y) :
    linFin P.rows y = linFin Q.rows y ∧ phaseAt n P y.val = phaseAt n Q y.val := by
  have h1 := congrFun h (linFin P.rows y)
  simp only [act, Pi.smul_apply, smul_eq_mul, basis, if_true, mul_one] at h1
  split_ifs at h1 with heq
  · exact ⟨heq, ωpow_injective (by simpa using h1)⟩
  · rw [mul_zero] at h1
    exact absurd h1 (ωpow_ne_zero _)

/-- Completeness: equivalent circuits of the fragment have the same form. -/
theorem complete {a b : Circuit n} {P Q : PhasePoly} (ha : nf a = some P) (hb : nf b = some Q)
    (h : a ≡ᵤ b) : P = Q := by
  have hact : ∀ y, P.act y = Q.act y := fun y => by
    rw [← nf_sound ha, ← nf_sound hb]
    exact h _
  refine ext_of_agree (wf_nf ha) (wf_nf hb) (fun i hi => ?_)
    (fun y hy => (act_inj (hact ⟨y, hy⟩)).2)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · have hl := (act_inj (hact ⟨2 ^ j, Nat.pow_lt_pow_right one_lt_two hj⟩)).1
    have hb := congrArg (bit ⟨i, hi⟩) hl
    rwa [bit_linFin, bit_linFin, Nat.land_comm, parityBelow_two_pow_land hj,
      Nat.land_comm, parityBelow_two_pow_land hj] at hb
  · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (not_lt.1 hj)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row_lt _ _ _) hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (row_lt _ _ _) hle)]

/-- The refutation check: both circuits are in the fragment and their forms
differ. -/
def refutes (a b : Circuit n) : Bool :=
  match nf a, nf b with
  | some P, some Q => decide (P ≠ Q)
  | _, _ => false

/-- A `true` refutation is a proof of inequivalence. -/
theorem refutes_sound {a b : Circuit n} (h : refutes a b = true) : ¬ a ≡ᵤ b := by
  unfold refutes at h
  split at h
  · next P Q ha hb =>
    intro hab
    exact of_decide_eq_true h (complete ha hb hab)
  · exact absurd h Bool.false_ne_true

end PhasePoly

/-! ### Exports -/

/-- The phase-polynomial canonical form of the CNOT-plus-diagonal fragment. -/
def phasePolyNormalForm (n : ℕ) : NormalForm n where
  NF := PhasePoly
  nf := PhasePoly.nf
  sound _ _ _ ha hb := PhasePoly.sound ha hb

/-- The phase-polynomial checker: both sides normalise to the same form. -/
def phasePolyChecker (n : ℕ) : Checker n := (phasePolyNormalForm n).toChecker

/-- The phase-polynomial refuter: both sides are in the fragment and their
forms differ. -/
def phasePolyRefutes (n : ℕ) (a b : Circuit n) : Bool := PhasePoly.refutes a b

/-- A `true` refutation proves inequivalence. -/
theorem phasePolyRefutes_sound {a b : Circuit n} (h : phasePolyRefutes n a b = true) :
    ¬ a ≡ᵤ b :=
  PhasePoly.refutes_sound h

/-- Within the fragment the checker is a decision procedure: `false` is a
refutation. -/
theorem phasePolyChecker_check_iff {a b : Circuit n} {P Q : PhasePoly}
    (ha : PhasePoly.nf a = some P) (hb : PhasePoly.nf b = some Q) :
    (phasePolyChecker n).check a b = true ↔ a ≡ᵤ b := by
  refine ⟨(phasePolyChecker n).sound a b, fun h => ?_⟩
  have hPQ := PhasePoly.complete ha hb h
  subst hPQ
  simp [phasePolyChecker, NormalForm.toChecker, phasePolyNormalForm, ha, hb]

/-! ### Tests

Each is a theorem proved by the checker: the kernel runs `nf` on both sides
and compares the forms. None enumerates a basis. `decide +kernel` is the
form to use; bare `decide` also closes windows this small, but the
elaborator's evaluator hits the default heartbeat limit at about a hundred
gates on ten wires, where the kernel needs a fraction of a second. -/

namespace PhasePoly.Tests

open Instr

/-- `T · T = S`. -/
theorem T_T_eq_S : ([T 0, T 0] : Circuit 1) ≡ᵤ [S 0] :=
  (phasePolyChecker 1).sound _ _ (by decide +kernel)

/-- A phase on the control commutes through a CNOT. -/
theorem T_cnot_comm : ([T 0, CX 0 1] : Circuit 2) ≡ᵤ [CX 0 1, T 0] :=
  (phasePolyChecker 2).sound _ _ (by decide +kernel)

/-- Two phase gadgets on the same parity merge. -/
theorem gadgets_merge :
    ([CX 0 1, T 1, CX 0 1, CX 0 1, T 1, CX 0 1] : Circuit 2) ≡ᵤ [CX 0 1, S 1, CX 0 1] :=
  (phasePolyChecker 2).sound _ _ (by decide +kernel)

/-- The `tof_3` merge window, on the five-wire register. -/
theorem tof3_merge : ([T 0, T 0] : Circuit 5) ≡ᵤ [S 0] :=
  (phasePolyChecker 5).sound _ _ (by decide +kernel)

/-- The control-side pattern of the two outer Toffolis of `tof_3` on wires
`0, 1`: PyZX merged the two `T 0` into one `S 0` at the front and moved each
`T 1` past the phase gadget `CX 0 1; T† 1; CX 0 1`. -/
theorem tof3_controls :
    ([T 1, CX 0 1, T 0, Tdg 1, CX 0 1, T 1, CX 0 1, T 0, Tdg 1, CX 0 1] : Circuit 5) ≡ᵤ
      [S 0, T 1, CX 0 1, Tdg 1, CX 0 1, T 1, CX 0 1, Tdg 1, CX 0 1] :=
  (phasePolyChecker 5).sound _ _ (by decide +kernel)

/-- The CNOT-plus-`T` core of a Toffoli on wires `0, 1, 3` of `tof_3`, with
the control phase `T 1` moved to the front. -/
theorem tof3_core :
    ([CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 1, T 3] : Circuit 5) ≡ᵤ
      [T 1, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 3] :=
  (phasePolyChecker 5).sound _ _ (by decide +kernel)

/-! The three relations among parities over `ℤ/8` that the parity-basis
form could not see; each is now an equality of canonical forms. -/

/-- `Z` on the parity `a ⊕ b` is `Z a · Z b`. -/
theorem Z_parity : ([CX 0 1, Z 1, CX 0 1] : Circuit 2) ≡ᵤ [Z 0, Z 1] :=
  (phasePolyChecker 2).sound _ _ (by decide +kernel)

/-- On three wires, `S` on each of the seven parities is the identity. -/
theorem seven_S :
    ([S 0, S 1, S 2, CX 0 1, S 1, CX 0 1, CX 0 2, S 2, CX 0 2, CX 1 2, S 2, CX 1 2,
      CX 0 2, CX 1 2, S 2, CX 1 2, CX 0 2] : Circuit 3) ≡ᵤ [] :=
  (phasePolyChecker 3).sound _ _ (by decide +kernel)

/-- On four wires, `T` on each of the fifteen parities is the identity. -/
theorem fifteen_T :
    ([T 0, T 1, T 2, T 3,
      CX 0 1, T 1, CX 0 1, CX 0 2, T 2, CX 0 2, CX 0 3, T 3, CX 0 3,
      CX 1 2, T 2, CX 1 2, CX 1 3, T 3, CX 1 3, CX 2 3, T 3, CX 2 3,
      CX 0 2, CX 1 2, T 2, CX 1 2, CX 0 2, CX 0 3, CX 1 3, T 3, CX 1 3, CX 0 3,
      CX 0 3, CX 2 3, T 3, CX 2 3, CX 0 3, CX 1 3, CX 2 3, T 3, CX 2 3, CX 1 3,
      CX 0 3, CX 1 3, CX 2 3, T 3, CX 2 3, CX 1 3, CX 0 3] : Circuit 4) ≡ᵤ [] :=
  (phasePolyChecker 4).sound _ _ (by decide +kernel)

/-- Phases on different parities do not merge, and by completeness the
checker's `false` is a refutation. -/
theorem not_merged : ¬ (([T 1, CX 0 1, T 1] : Circuit 2) ≡ᵤ [S 1, CX 0 1]) :=
  phasePolyRefutes_sound (by decide +kernel)

/-- `T` on a CNOT target does not commute with the CNOT: refuted on the
two-wire fragment without a basis vector. -/
theorem not_T_target_comm : ¬ (([T 1, CX 0 1] : Circuit 2) ≡ᵤ [CX 0 1, T 1]) :=
  phasePolyRefutes_sound (by decide +kernel)

/-- A refutation needs both sides in the fragment: `H` makes it decline. -/
theorem refutes_H : phasePolyRefutes 1 [H 0] [H 0] = false := by decide +kernel

/-- A Hadamard is outside the fragment. -/
theorem nf_H : PhasePoly.nf ([H 0] : Circuit 1) = none := by decide +kernel

/-- A CNOT whose control is its target is outside the fragment. -/
theorem nf_cnot_self : PhasePoly.nf ([CX 0 0] : Circuit 1) = none := by decide +kernel

end PhasePoly.Tests

end Quantum.Circuit
