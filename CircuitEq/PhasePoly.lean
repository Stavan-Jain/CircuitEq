/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Lanes
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

* `rows : ℕ`, the `n` rows packed into one `Nat` of `n²` bits, row `i` in
  bits `[n·i, n·(i+1))` and read by `PhasePoly.row n R i`, each a bitmask in
  the encoding of `CircuitEq.Support` (bit `j` of row `i` is set iff input
  `j` is in the parity wire `i` holds);
* `deg1`, `deg2`, `deg3 : Lanes` (`CircuitEq.Lanes`), the coefficients of
  the monomials of each degree as *bit planes*: three `Nat`s whose bit `t`
  are the three bits of the residue in lane `t`. Lane `i` holds `a_i`, lane
  `tri j + i` (for `i < j`) holds `a_{ij}`, lane `tet l + tri j + i` (for
  `i < j < l`) holds `a_{ijl}`, where `tri j = C(j, 2)` and
  `tet l = C(l, 3)`; every other lane is zero.

A diagonal gate is up to three plane additions: `Lanes.addOn` adds a constant on
every lane of a mask by a three-bit ripple-carry adder on planes, a fixed number
of `Nat` bit operations however many lanes the mask names, and the masks of the
pairs and triples inside `m` (`Lanes.pairMask`, `Lanes.tripMask`) are one
shift-and-or per set bit of `m` (`Lanes.maskFold`). Phases are in units of
`π/4`: `T = 1`, `S = 2`, `Z = 4`, `S† = 6`, `T† = 7`.

`PhasePoly.nf` is the normaliser: `none` at the first gate outside the
fragment, including a CNOT whose control is its target (not unitary).
`phasePolyNormalForm n` packages it as a `NormalForm n` and
`phasePolyChecker n` is its checker. `CircuitEq.PhasePoly.Complete` proves
the form canonical and exports `phasePolyRefutes`, the other direction, a
`Bool` whose `true` proves `¬ a ≡ᵤ b`.

## Soundness and completeness

The invariant is on basis vectors: `PhasePoly.act P y` is
`ω ^ φ(y) • basis (A y)`, with `A y` read from the rows (`linFin`, bit `i` the
parity of `row n R i &&& y`) and `φ(y)` the polynomial evaluated at `y`
(`phaseAt`, sums over `Finset.range` in `ZMod 8`, never evaluated by the
kernel). `phaseAt_diag` is the heart: the plane additions add exactly
`k · (m · y)`, by the lane lemmas `Lanes.lane_addOn`, the mask lemmas
`Lanes.testBit_pairMask` and `Lanes.testBit_tripMask`, and the count identity
`cnt_parity` (`cnt1 − 2·cnt2 + 4·cnt3 = parity` in `ZMod 8`, by induction on the
wires). `run_sound` then tracks `Instr.apply` step by step and `sound` closes
with `equivalent_iff_basis`.

Completeness (`PhasePoly.complete`, in `CircuitEq.PhasePoly.Complete`):
equal unitaries give equal forms, because the action on `|y⟩` determines
`A y` and `φ(y)`, `A` on the unit vectors determines the rows, and `φ` on
the inputs of weight one, two and three determines the coefficients degree
by degree (`phaseAt_two_pow` and its two companions), while the invariant
`WF` (only the lanes of monomials and the bits of `n` rows are ever
non-zero) and `ext_of_agree` turn equal coefficients into equal planes. So
`phasePolyRefutes a b = true`, which is "both in the fragment and different
forms", proves `¬ a ≡ᵤ b` (`phasePolyRefutes_sound`), and for the fragment
`false` from the checker is a refutation, not merely "undecided".

## Kernel cost

`nf` is structural recursion over the circuit with `Nat` bit operations (`^^^`,
`&&&`, `|||`, `<<<`, `>>>`, `testBit`, `gcd`, all GMP-accelerated in the
kernel). Nothing of size `2 ^ n` is built; the planes are `n`, `C(n,2)` and
`C(n,3)` bits and the rows `n²` bits. A CNOT is a shift and an xor. A phase gate
builds the pair and triple masks of its parity with `maskFold`, which visits
only the set bits of a sparse parity (`Lanes.sparseFold`: lowest set bit by
`gcd`, its index by a population count checked on the 1024 powers of two below
the word width) and tests every index of a dense one (`Lanes.bitFold`), and
skips a plane it would add nothing to (`Lanes.addOnz`). Measured on an Apple M4
with cached imports (`benchmarks/scale/README.md`), each pair with a
gate-deleted mutant refuted: random CNOT-plus-`T` circuits of 200, 400 and 800
gates on 20, 40 and 80 wires against their PyZX phase-folded forms in 0.2, 0.6
and 1.9 s of kernel time at 1.9, 2.0 and 2.5 GB peak (the imports alone are 1.8
GB); networks of CCZ gadgets, every parity of weight at most three, of 3400,
6800 and 10200 gates on 100, 200 and 300 wires in 2.8, 5.9 and 10.1 s at 2.7,
3.8 and 5.3 GB. What grows is the triple plane: 164 KB at 200 wires, and the
kernel copies it at every gate that changes it. Two traps found on the way, both
about what the kernel retains or re-walks rather than about arithmetic: a row
table kept as a `List ℕ` cost 1.5 MB of retained terms per CNOT, and a plane
passed through unchanged *inside* `add` made every later gate re-walk the chain
of pass-through terms, quadratic time (see `Lanes.addOnz`). Use
`decide +kernel`; the elaborator's own evaluator (bare `decide`, `rfl`) exhausts
the default heartbeat limit at about a hundred gates. -/

namespace Quantum.Circuit

open Finset

variable {n : ℕ}
open Lanes (tri tet pairMask tripMask testBit_pairMask testBit_tripMask)

/-! ### Phases and basis vectors -/

namespace PhasePoly

/-- `ω ^ k` for a phase `k : ZMod 8`, in units of `π/4`. -/
def ωpow (k : ZMod 8) : Zeta8 := Zeta8.ω ^ k.val

/-- The zero phase is the scalar `1`. -/
@[simp] lemma ωpow_zero : ωpow 0 = 1 := by simp [ωpow]

/-- Phases add modulo 8 because `ω ^ 8 = 1`. -/
lemma ωpow_add (a b : ZMod 8) : ωpow (a + b) = ωpow a * ωpow b := by
  rw [ωpow, ωpow, ωpow, ZMod.val_add, Zeta8.ω_pow_mod, pow_add]

/-- `ω` has order eight: distinct phases give distinct scalars. -/
lemma ωpow_injective : Function.Injective ωpow := by
  intro a b h
  revert a b
  decide +kernel

/-- No phase is the scalar `0`. -/
lemma ωpow_ne_zero (k : ZMod 8) : ωpow k ≠ 0 := by
  revert k
  decide +kernel

end PhasePoly

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
    g.mat b b = PhasePoly.ωpow (if b then k else 0) := by
  cases g <;> simp only [Gate1.phase?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    cases b <;> decide +kernel

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

end PhasePoly

/-! ### Exports -/


/-- The phase-polynomial canonical form of the CNOT-plus-diagonal fragment. -/
def phasePolyNormalForm (n : ℕ) : NormalForm n where
  NF := PhasePoly
  nf := PhasePoly.nf
  sound _ _ _ ha hb := PhasePoly.sound ha hb

/-- The phase-polynomial checker: both sides normalise to the same form. -/
def phasePolyChecker (n : ℕ) : Checker n := (phasePolyNormalForm n).toChecker

end Quantum.Circuit
