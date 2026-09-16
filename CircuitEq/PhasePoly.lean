/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Structural
import CircuitEq.Support
import CircuitEq.Checker

/-!
# Phase polynomials: a certified normal form for CNOT-plus-diagonal circuits

A circuit of CNOTs and diagonal gates (`Z`, `S`, `S†`, `T`, `T†`) sends each
basis state `|y⟩` to `ω ^ φ(y) |A y⟩`, where `A` is an invertible
`𝔽₂`-linear map and `φ : 𝔽₂ⁿ → ℤ/8` is a *phase polynomial*, a sum of terms
`k · (m · y)` over parities `m · y` of the input bits. Both are read off the
circuit in one pass with no state vector: a CNOT `c t` replaces row `t` of
`A` by `row t ⊕ row c`, and a diagonal gate of phase `k` on wire `i` adds
`k` to the coefficient of the parity wire `i` currently holds. This is the
representation T-count optimisers work in, so two circuits an optimiser
related by merging, commuting or cancelling phase gadgets have the same
form, and the checker decides the pair symbolically at a cost linear in the
gate count and independent of `2 ^ n`.

## The form

`PhasePoly` is `rows : List ℕ`, one bitmask per wire in the encoding of
`CircuitEq.Support` (bit `j` of `rows[i]` is set iff input `j` is in the
parity wire `i` holds), and `terms : List (ℕ × Fin 8)`, the phase
polynomial as `(mask, phase)` pairs kept sorted by mask with zero phases
dropped, so that equality of forms is syntactic (`DecidableEq`). Phases are
in units of `π/4`: `T = 1`, `S = 2`, `Z = 4`, `S† = 6`, `T† = 7`.

`PhasePoly.nf` is the normaliser: `none` at the first gate outside the
fragment, including a CNOT whose control is its target (not unitary).
`phasePolyNormalForm n` packages it as a `NormalForm n` and
`phasePolyChecker n` is its checker.

## Soundness

The invariant is on basis vectors: `PhasePoly.act p y` is
`ω ^ φ(y) • basis (A y)`, with `A y` read from the rows (`PhasePoly.linFin`,
bit `i` the parity of `rows[i] &&& y`) and `φ(y)` summed from the terms
(`PhasePoly.phaseAt`). `PhasePoly.run_sound` shows each step of the
normaliser tracks `Instr.apply`, through the two basis facts
`applyCNOT_basis` and `applyOne_basis_of_diag`, and `PhasePoly.sound` closes
with `equivalent_iff_basis`. Completeness (equivalent fragment circuits have
equal forms) holds for this canonical representation but is not proved, and
resynthesis of a circuit from a form is left for the optimiser.

## Kernel cost

`nf` is structural recursion over the circuit with `Nat` bit operations
(`^^^`, `&&&`, `2 ^ i`, all GMP-accelerated in the kernel), `List.set` and
`List.getD` on an `n`-element list, and a sorted insertion into the term
list. Nothing of size `2 ^ n` is built. The semantic side (`parityBelow`,
`linNat`) exists only for the proofs and is never evaluated. Measured with
cached imports: each test window below costs under 40 ms of kernel time,
and a synthetic 101-gate CNOT-plus-`T` circuit on ten wires against its
55-gate phase-merged form costs about 0.2 s, where a basis enumeration on
ten wires is out of reach. The three-wire Toffoli core in the tests costs
about 8 s by basis enumeration (`decide +kernel` on `≡ᵤ`) and 30 ms here.
Use `decide +kernel`: the elaborator's own evaluator (bare `decide`, `rfl`)
exhausts the default heartbeat limit on the 101-gate pair.
-/

namespace Quantum.Circuit

variable {n : ℕ}

/-! ### Phases and basis vectors -/

/-- `ω ^ k` for a phase `k : Fin 8`, in units of `π/4`. -/
def ωpow (k : Fin 8) : Zeta8 := Zeta8.ω ^ k.val

/-- The zero phase is the scalar `1`. -/
@[simp] lemma ωpow_zero : ωpow 0 = 1 := pow_zero _

/-- Phases add modulo 8 because `ω ^ 8 = 1`. -/
lemma ωpow_add (a b : Fin 8) : ωpow (a + b) = ωpow a * ωpow b := by
  unfold ωpow
  rw [Fin.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 8]
  rw [pow_add, pow_mul, Zeta8.ω_pow_eight, one_pow, mul_one]

/-- The phase of a diagonal gate `diag(1, ω ^ k)`, in units of `π/4`; `none`
for `H`, `X`, `Y`. -/
def Gate1.phase? : Gate1 → Option (Fin 8)
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
lemma Gate1.isDiag_of_phase? {g : Gate1} {k : Fin 8} (h : g.phase? = some k) :
    g.isDiag = true := by
  rw [← Gate1.phase?_isSome, h]; rfl

/-- The diagonal of a gate with phase `k` is `(1, ω ^ k)`. -/
lemma Gate1.mat_diag_of_phase? {g : Gate1} {k : Fin 8} (h : g.phase? = some k) (b : Bool) :
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

/-! ### The form -/

/-- The phase-polynomial normal form of a CNOT-plus-diagonal circuit. -/
structure PhasePoly where
  /-- Row `i` is the bitmask of input wires whose parity wire `i` holds. -/
  rows : List ℕ
  /-- The phase polynomial: `(mask, phase)` pairs sorted by mask, no zero
  phases. -/
  terms : List (ℕ × Fin 8)
  deriving DecidableEq, Repr

namespace PhasePoly

/-! #### The normaliser (kernel side) -/

/-- Add phase `k` to the coefficient of mask `m`, keeping the list sorted by
mask and dropping a coefficient that becomes zero. -/
def insertPhase (m : ℕ) (k : Fin 8) : List (ℕ × Fin 8) → List (ℕ × Fin 8)
  | [] => [(m, k)]
  | (m', k') :: rest =>
    if m < m' then (m, k) :: (m', k') :: rest
    else if m = m' then (if k + k' = 0 then rest else (m, k + k') :: rest)
    else (m', k') :: insertPhase m k rest

/-- Add phase `k` to the coefficient of mask `m`; a zero phase changes
nothing. -/
def addPhase (m : ℕ) (k : Fin 8) (p : List (ℕ × Fin 8)) : List (ℕ × Fin 8) :=
  if k = 0 then p else insertPhase m k p

/-- The identity linear part on `n` wires: wire `i` holds input `i`. -/
def initRows (n : ℕ) : List ℕ := (List.range n).map (2 ^ ·)

/-- The form of the empty circuit. -/
def init (n : ℕ) : PhasePoly := ⟨initRows n, []⟩

/-- The row update of a CNOT: row `t` gains row `c`. -/
def cnotRows (rows : List ℕ) (c t : ℕ) : List ℕ := rows.set t (rows.getD t 0 ^^^ rows.getD c 0)

/-- Apply a CNOT with control `c` and target `t`. -/
def cnot (p : PhasePoly) (c t : ℕ) : PhasePoly := { p with rows := cnotRows p.rows c t }

/-- Apply a diagonal gate of phase `k` on wire `i`. -/
def diag (p : PhasePoly) (i : ℕ) (k : Fin 8) : PhasePoly :=
  { p with terms := addPhase (p.rows.getD i 0) k p.terms }

/-- One instruction; `none` outside the fragment. A CNOT whose control is
its target is rejected: it is not a permutation of the basis. -/
def step (p : PhasePoly) : Instr n → Option PhasePoly
  | .cnot c t => if c = t then none else some (p.cnot c.val t.val)
  | .one g i =>
    match g.phase? with
    | some k => some (p.diag i.val k)
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

/-! #### The semantics (proof side) -/

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

/-- The output index of the linear part on input `y`, built bit by bit:
bit `i` is the parity of `rows[i] &&& y` over the low `w` bit positions. -/
def linNat (w : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, y => Nat.bit (parityBelow w (r &&& y)) (linNat w rs y)

/-- Bit `i` of `linNat` is the parity of `rows[i] &&& y`, with `0` for a
missing row. -/
lemma testBit_linNat (w : ℕ) (rows : List ℕ) (y i : ℕ) :
    (linNat w rows y).testBit i = parityBelow w (rows.getD i 0 &&& y) := by
  induction rows generalizing i with
  | nil => simp [linNat]
  | cons r rs ih =>
    cases i with
    | zero => simp [linNat]
    | succ i => simp [linNat, Nat.testBit_bit_succ, ih]

/-- The output basis index of the linear part on input `y`. -/
def linFin (rows : List ℕ) (y : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨linNat n rows y.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- Bit `i` of the output index is the parity of `rows[i] &&& y`. -/
lemma bit_linFin (rows : List ℕ) (y : Fin (2 ^ n)) (i : Fin n) :
    bit i (linFin rows y) = parityBelow n (rows.getD i.val 0 &&& y.val) := by
  simp [bit, linFin, Nat.testBit_mod_two_pow, i.isLt, testBit_linNat]

/-- Reading back an in-range `List.set` at its own index. -/
lemma getD_set_self {l : List ℕ} {i : ℕ} (h : i < l.length) (v : ℕ) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self h]

/-- A `List.set` leaves every other index alone. -/
lemma getD_set_ne {l : List ℕ} {i j : ℕ} (h : i ≠ j) (v : ℕ) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- The row update of a CNOT is the CNOT's action on the output index. -/
lemma linFin_cnotRows {rows : List ℕ} (hlen : rows.length = n) {c t : Fin n} (hct : c ≠ t)
    (y : Fin (2 ^ n)) :
    linFin (cnotRows rows c.val t.val) y =
      if bit c (linFin rows y) then flipBit t (linFin rows y) else linFin rows y := by
  apply eq_of_bit_eq
  intro j
  rw [bit_linFin]
  by_cases hjt : j = t
  · subst hjt
    rw [cnotRows, getD_set_self (hlen ▸ j.isLt), Nat.and_xor_distrib_right, parityBelow_xor,
      ← bit_linFin, ← bit_linFin]
    cases bit c (linFin rows y) <;> simp
  · have hjt' : t.val ≠ j.val := fun e => hjt (Fin.ext e).symm
    rw [cnotRows, getD_set_ne hjt', ← bit_linFin]
    cases bit c (linFin rows y) <;> simp [bit_flipBit_of_ne hjt]

/-- The identity rows have one row per wire. -/
@[simp] lemma initRows_length (n : ℕ) : (initRows n).length = n := by simp [initRows]

/-- Row `i` of the identity rows is the single bit `i`. -/
lemma initRows_getD {i : ℕ} (h : i < n) : (initRows n).getD i 0 = 2 ^ i := by
  simp [initRows, List.getD_eq_getElem?_getD, List.getElem?_range h]

/-- The identity rows give the identity map. -/
lemma linFin_initRows (y : Fin (2 ^ n)) : linFin (initRows n) y = y :=
  eq_of_bit_eq fun i => by
    rw [bit_linFin, initRows_getD i.isLt, parityBelow_two_pow_land i.isLt]; rfl

/-- The phase polynomial evaluated on input `y`. -/
def phaseAt (p : List (ℕ × Fin 8)) (y : Fin (2 ^ n)) : Fin 8 :=
  p.foldr (fun mk acc => (if parityBelow n (mk.1 &&& y.val) then mk.2 else 0) + acc) 0

/-- The empty polynomial is the zero phase. -/
@[simp] lemma phaseAt_nil (y : Fin (2 ^ n)) : phaseAt [] y = 0 := rfl

/-- A term contributes its phase exactly when its parity is odd. -/
@[simp] lemma phaseAt_cons (m : ℕ) (k : Fin 8) (p : List (ℕ × Fin 8)) (y : Fin (2 ^ n)) :
    phaseAt ((m, k) :: p) y = (if parityBelow n (m &&& y.val) then k else 0) + phaseAt p y := rfl

/-- Insertion in front of a larger mask. -/
lemma insertPhase_cons_lt {m m' : ℕ} (h : m < m') (k k' : Fin 8) (rest : List (ℕ × Fin 8)) :
    insertPhase m k ((m', k') :: rest) = (m, k) :: (m', k') :: rest := by
  simp [insertPhase, h]

/-- Insertion on an equal mask whose phases cancel drops the term. -/
lemma insertPhase_cons_eq_zero {m : ℕ} {k k' : Fin 8} (h : k + k' = 0)
    (rest : List (ℕ × Fin 8)) : insertPhase m k ((m, k') :: rest) = rest := by
  simp [insertPhase, h]

/-- Insertion on an equal mask merges the phases. -/
lemma insertPhase_cons_eq {m : ℕ} {k k' : Fin 8} (h : k + k' ≠ 0) (rest : List (ℕ × Fin 8)) :
    insertPhase m k ((m, k') :: rest) = (m, k + k') :: rest := by
  simp [insertPhase, h]

/-- Insertion past a smaller mask recurses. -/
lemma insertPhase_cons_gt {m m' : ℕ} (h : m' < m) (k k' : Fin 8) (rest : List (ℕ × Fin 8)) :
    insertPhase m k ((m', k') :: rest) = (m', k') :: insertPhase m k rest := by
  have h1 : ¬ m < m' := by omega
  have h2 : m ≠ m' := by omega
  simp [insertPhase, h1, h2]

/-! The two facts about `Fin 8` addition the merge lemma needs; the algebraic
instances on `Fin` are not in this import closure, and `omega` settles them. -/

/-- Associativity of `Fin 8` addition. -/
lemma fin8_add_assoc (a b c : Fin 8) : a + b + c = a + (b + c) := by
  apply Fin.ext; simp only [Fin.val_add]; omega

/-- Left commutativity of `Fin 8` addition. -/
lemma fin8_add_left_comm (a b c : Fin 8) : a + (b + c) = b + (a + c) := by
  apply Fin.ext; simp only [Fin.val_add]; omega

/-- Inserting a term adds its contribution. -/
lemma phaseAt_insertPhase (m : ℕ) (k : Fin 8) (p : List (ℕ × Fin 8)) (y : Fin (2 ^ n)) :
    phaseAt (insertPhase m k p) y =
      (if parityBelow n (m &&& y.val) then k else 0) + phaseAt p y := by
  induction p with
  | nil => simp [insertPhase]
  | cons mk rest ih =>
    obtain ⟨m', k'⟩ := mk
    rcases Nat.lt_trichotomy m m' with h | rfl | h
    · rw [insertPhase_cons_lt h, phaseAt_cons]
    · by_cases h3 : k + k' = 0
      · rw [insertPhase_cons_eq_zero h3, phaseAt_cons]
        split_ifs
        · rw [← fin8_add_assoc, h3, Fin.zero_add]
        · rw [Fin.zero_add, Fin.zero_add]
      · rw [insertPhase_cons_eq h3, phaseAt_cons, phaseAt_cons]
        split_ifs
        · exact fin8_add_assoc _ _ _
        · rw [Fin.zero_add, Fin.zero_add]
    · rw [insertPhase_cons_gt h, phaseAt_cons, phaseAt_cons, ih, fin8_add_left_comm]

/-- Adding a phase adds its contribution. -/
lemma phaseAt_addPhase (m : ℕ) (k : Fin 8) (p : List (ℕ × Fin 8)) (y : Fin (2 ^ n)) :
    phaseAt (addPhase m k p) y = (if parityBelow n (m &&& y.val) then k else 0) + phaseAt p y := by
  by_cases hk : k = 0
  · subst hk; simp [addPhase]
  · rw [addPhase, if_neg hk]; exact phaseAt_insertPhase m k p y

/-- The action of a form on a basis vector: a phase times a basis vector. -/
def act (p : PhasePoly) (y : Fin (2 ^ n)) : Vec n :=
  ωpow (phaseAt p.terms y) • basis (linFin p.rows y)

/-- The form of the empty circuit acts as the identity. -/
lemma act_init (y : Fin (2 ^ n)) : (init n).act y = basis y := by
  simp [act, init, linFin_initRows]

/-! #### Soundness -/

/-- A step keeps the number of rows. -/
lemma rows_length_step {p p' : PhasePoly} {g : Instr n} (h : p.step g = some p') :
    p'.rows.length = p.rows.length := by
  cases g with
  | cnot c t =>
    by_cases hct : c = t
    · simp [step, hct] at h
    · simp only [step, hct, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [cnot, cnotRows]
  | one g i =>
    cases hg : g.phase? with
    | none => simp [step, hg] at h
    | some k =>
      simp only [step, hg, Option.some.injEq] at h
      subst h
      rfl

/-- One step of the normaliser tracks the instruction's action. -/
lemma apply_act {p p' : PhasePoly} (hlen : p.rows.length = n) {g : Instr n}
    (h : p.step g = some p') (y : Fin (2 ^ n)) : g.apply (p.act y) = p'.act y := by
  cases g with
  | cnot c t =>
    by_cases hct : c = t
    · simp [step, hct] at h
    · simp only [step, hct, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [act, Instr.apply_cnot, applyCNOT_smul, applyCNOT_basis hct, cnot,
        linFin_cnotRows hlen hct]
  | one g i =>
    cases hg : g.phase? with
    | none => simp [step, hg] at h
    | some k =>
      simp only [step, hg, Option.some.injEq] at h
      subst h
      have hoff := Gate1.mat_off_diag_of_isDiag (Gate1.isDiag_of_phase? hg)
      simp only [act, Instr.apply_one, applyOne_smul, applyOne_basis_of_diag hoff,
        Gate1.mat_diag_of_phase? hg, diag, phaseAt_addPhase, ωpow_add, bit_linFin, smul_smul]
      rw [mul_comm]

/-- The normaliser tracks the denotation from any starting form. -/
theorem run_sound {c : Circuit n} {p x : PhasePoly} (hlen : p.rows.length = n)
    (h : run c p = some x) (y : Fin (2 ^ n)) : denote c (p.act y) = x.act y := by
  induction c generalizing p with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    rfl
  | cons g c ih =>
    simp only [run] at h
    cases hs : p.step g with
    | none => simp [hs] at h
    | some p' =>
      simp only [hs] at h
      rw [denote_cons, apply_act hlen hs, ih (by rw [rows_length_step hs, hlen]) h]

/-- A normal form describes the circuit's action on every basis vector. -/
theorem nf_sound {c : Circuit n} {x : PhasePoly} (h : nf c = some x) (y : Fin (2 ^ n)) :
    denote c (basis y) = x.act y := by
  rw [← act_init y]
  exact run_sound (initRows_length n) h y

/-- Equal normal forms are equivalent circuits. -/
theorem sound {a b : Circuit n} {x : PhasePoly} (ha : nf a = some x) (hb : nf b = some x) :
    a ≡ᵤ b :=
  (equivalent_iff_basis a b).2 fun y => (nf_sound ha y).trans (nf_sound hb y).symm

end PhasePoly

/-! ### Exports -/

/-- The phase-polynomial normal form of the CNOT-plus-diagonal fragment. -/
def phasePolyNormalForm (n : ℕ) : NormalForm n where
  NF := PhasePoly
  nf := PhasePoly.nf
  sound _ _ _ ha hb := PhasePoly.sound ha hb

/-- The phase-polynomial checker: both sides normalise to the same form. -/
def phasePolyChecker (n : ℕ) : Checker n := (phasePolyNormalForm n).toChecker

/-! ### Tests

Each is a theorem proved by the checker: the kernel runs `nf` on both sides
and compares the forms. None enumerates a basis. `decide +kernel` is the
form to use; bare `decide` also closes windows this small, but the
elaborator's evaluator hits the default heartbeat limit at about a hundred
gates on ten wires, where the kernel needs 0.2 s. -/

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

/-- Phases on different parities do not merge: the checker declines. -/
theorem not_merged :
    (phasePolyChecker 2).check [T 1, CX 0 1, T 1] [S 1, CX 0 1] = false := by decide +kernel

/-- A Hadamard is outside the fragment. -/
theorem nf_H : PhasePoly.nf ([H 0] : Circuit 1) = none := by decide +kernel

/-- A CNOT whose control is its target is outside the fragment. -/
theorem nf_cnot_self : PhasePoly.nf ([CX 0 0] : Circuit 1) = none := by decide +kernel

end PhasePoly.Tests

end Quantum.Circuit
