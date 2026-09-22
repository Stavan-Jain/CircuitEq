/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.PhasePoly

/-!
# Completeness of the phase-polynomial form, and the refuter

`PhasePoly.complete`: two circuits of the CNOT-plus-diagonal fragment with
the same unitary have the same normal form. So the form is canonical, the
checker of `CircuitEq.PhasePoly` is a decision procedure on the fragment
(`phasePolyChecker_check_iff`), and different forms prove inequivalence
(`phasePolyRefutes`, `phasePolyRefutes_sound`). Kept apart from the checker
because nothing that only proves equivalences needs it.
-/

namespace Quantum.Circuit

open Finset

variable {n : ℕ}

open Lanes (tri tet pairMask tripMask pairMask_lane tripMask_lane)

namespace PhasePoly

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

end Quantum.Circuit
