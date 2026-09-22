/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Bits
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Bit planes: residues modulo 8 on many lanes at once

The arithmetic the phase-polynomial checker (`CircuitEq.PhasePoly`) runs on,
kept apart because nothing in it is about circuits. A `Lanes` is a vector of
residues modulo 8 indexed by `ℕ`, stored as three `Nat` bit planes, so adding
a constant on every lane of a mask is a fixed number of bit operations
(`Lanes.addOn`, a three-bit ripple-carry adder on planes). The second half
numbers the pairs and triples of wires in the combinatorial number system
(`Lanes.tri`, `Lanes.tet`) and builds, for a parity `m`, the masks of the
pairs and triples inside it (`Lanes.pairMask`, `Lanes.tripMask`) by one
shift-and-or per set bit (`Lanes.maskFold`), visiting only the set bits of a
sparse parity. Every operation is a `Nat` operation the kernel accelerates;
`Nat.log2` is not, so set bits are found with `gcd` and a population count.
-/

namespace Quantum.Circuit

variable {n : ℕ}

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

namespace Lanes

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


end Lanes

end Quantum.Circuit
