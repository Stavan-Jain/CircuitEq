/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Zeta8
import CircuitEq.Bits
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# Clifford+T gates and their sparse action on state vectors

The gate alphabet is the single-qubit Clifford+T set `H, X, Y, Z, S, S†, T,
T†` (`Gate1`, each with a `2 × 2` matrix over `ℚ(ζ₈)` in `Gate1.mat`) plus
`CNOT`. Every other Clifford+T gate (`CZ`, `SWAP`, `Toffoli` via its
Clifford+T decomposition, …) is a circuit over these.

## Sparse pointwise semantics

Rather than building the `2 ^ n × 2 ^ n` matrix `I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I`, a gate
acts directly on amplitude vectors `Vec n = Fin (2 ^ n) → ℚ(ζ₈)`:

```
applyOne G i ψ x  = G[b, b] · ψ x + G[b, ¬b] · ψ (flipBit i x)  (b = bit i x)
applyCNOT c t ψ x = if bit c x then ψ (flipBit t x) else ψ x
```

Each output amplitude reads at most two input amplitudes, so a gate costs
`O(1)` per entry and the whole thing is kernel-evaluable. The same shape makes
the algebra easy: gates on disjoint qubits commute (`applyOne_comm`,
`applyOne_applyCNOT_comm`) and gates on the same qubit compose to the matrix
product (`applyOne_applyOne_same`), by pointwise `ring` after the bit lemmas
from `CircuitEq.Bits`.
-/

namespace Quantum.Circuit

open Zeta8

/-- A single-qubit matrix over `ℚ(ζ₈)`, indexed by `Bool` (`false = |0⟩`,
`true = |1⟩`). -/
abbrev Mat1 := Matrix Bool Bool Zeta8

/-- The single-qubit Clifford+T gate alphabet. -/
inductive Gate1 where
  | H | X | Y | Z | S | Sdg | T | Tdg
  deriving DecidableEq, Repr

namespace Gate1

/-- The matrix of each gate, in the computational basis. -/
def mat : Gate1 → Mat1
  | H => Matrix.of fun r c => if r && c then -invSqrt2 else invSqrt2
  | X => Matrix.of fun r c => if r = c then 0 else 1
  | Y => Matrix.of fun r c => if r = c then 0 else if r then I else -I
  | Z => Matrix.of fun r c => if r = c then (if r then -1 else 1) else 0
  | S => Matrix.of fun r c => if r = c then (if r then I else 1) else 0
  | Sdg => Matrix.of fun r c => if r = c then (if r then -I else 1) else 0
  | T => Matrix.of fun r c => if r = c then (if r then ω else 1) else 0
  | Tdg => Matrix.of fun r c => if r = c then (if r then -ω ^ 3 else 1) else 0

/-! ### Single-qubit gate identities

These are `2 × 2` matrix equalities over the computable field, so the kernel
decides them. They are the leaves the structural proofs bottom out in. -/

lemma H_mul_H : H.mat * H.mat = 1 := by decide +kernel
lemma X_mul_X : X.mat * X.mat = 1 := by decide +kernel
lemma Y_mul_Y : Y.mat * Y.mat = 1 := by decide +kernel
lemma Z_mul_Z : Z.mat * Z.mat = 1 := by decide +kernel
lemma S_mul_S : S.mat * S.mat = Z.mat := by decide +kernel
lemma T_mul_T : T.mat * T.mat = S.mat := by decide +kernel
lemma S_mul_Sdg : S.mat * Sdg.mat = 1 := by decide +kernel
lemma Sdg_mul_S : Sdg.mat * S.mat = 1 := by decide +kernel
lemma T_mul_Tdg : T.mat * Tdg.mat = 1 := by decide +kernel
lemma Tdg_mul_T : Tdg.mat * T.mat = 1 := by decide +kernel
lemma H_mul_X_mul_H : H.mat * X.mat * H.mat = Z.mat := by decide +kernel
lemma H_mul_Z_mul_H : H.mat * Z.mat * H.mat = X.mat := by decide +kernel
lemma X_mul_Z : X.mat * Z.mat = -(Z.mat * X.mat) := by decide +kernel

/-- Whether a gate's matrix is diagonal: `Z`, `S`, `S†`, `T`, `T†`. -/
def isDiag : Gate1 → Bool
  | Z | S | Sdg | T | Tdg => true
  | H | X | Y => false

/-- A diagonal gate has zero off-diagonal entries. -/
lemma mat_off_diag_of_isDiag {g : Gate1} (h : g.isDiag = true) : ∀ b, g.mat b (!b) = 0 := by
  cases g <;> first | exact absurd h (by decide) | decide +kernel

/-- Diagonal gates commute as matrices. -/
lemma mat_comm_of_isDiag {g g' : Gate1} (h : g.isDiag = true) (h' : g'.isDiag = true) :
    g.mat * g'.mat = g'.mat * g.mat := by
  cases g <;> cases g' <;>
    first | exact absurd h (by decide) | exact absurd h' (by decide) | decide +kernel

end Gate1

/-- Amplitude vectors of an `n`-qubit register over `ℚ(ζ₈)`. -/
abbrev Vec (n : ℕ) := Fin (2 ^ n) → Zeta8

variable {n : ℕ}

/-- Apply the single-qubit matrix `G` to qubit `i` of `ψ`.

This is the textbook state-vector update: the new amplitude at basis index
`x` mixes the old amplitudes at `x` and at `x` with bit `i` flipped, weighted
by row `bit i x` of `G`. Only two amplitudes are consulted per output entry,
so the definition is sparse and involves no `2 ^ n × 2 ^ n` matrix. -/
def applyOne (G : Mat1) (i : Fin n) (ψ : Vec n) : Vec n :=
  fun x => G (bit i x) (bit i x) * ψ x + G (bit i x) (!bit i x) * ψ (flipBit i x)

/-- CNOT with control `c` and target `t`: permute amplitudes, flipping bit `t`
wherever bit `c` is set. -/
def applyCNOT (c t : Fin n) (ψ : Vec n) : Vec n :=
  fun x => if bit c x then ψ (flipBit t x) else ψ x

/-! ### Linearity -/

lemma applyOne_add (G : Mat1) (i : Fin n) (ψ φ : Vec n) :
    applyOne G i (ψ + φ) = applyOne G i ψ + applyOne G i φ := by
  funext x
  simp only [applyOne, Pi.add_apply]
  ring

lemma applyOne_smul (G : Mat1) (i : Fin n) (a : Zeta8) (ψ : Vec n) :
    applyOne G i (a • ψ) = a • applyOne G i ψ := by
  funext x
  simp only [applyOne, Pi.smul_apply, smul_eq_mul]
  ring

lemma applyCNOT_add (c t : Fin n) (ψ φ : Vec n) :
    applyCNOT c t (ψ + φ) = applyCNOT c t ψ + applyCNOT c t φ := by
  funext x
  simp only [applyCNOT, Pi.add_apply]
  split_ifs <;> rfl

lemma applyCNOT_smul (c t : Fin n) (a : Zeta8) (ψ : Vec n) :
    applyCNOT c t (a • ψ) = a • applyCNOT c t ψ := by
  funext x
  simp only [applyCNOT, Pi.smul_apply]
  split_ifs <;> rfl

/-! ### The algebra of gate applications -/

/-- Two gates on the same qubit compose to the matrix product (the later gate
is the left factor, as operators). -/
lemma applyOne_applyOne_same (A B : Mat1) (i : Fin n) (ψ : Vec n) :
    applyOne A i (applyOne B i ψ) = applyOne (A * B) i ψ := by
  funext x
  simp only [applyOne, bit_flipBit_self, flipBit_flipBit_self, Bool.not_not, Matrix.mul_apply,
    Fintype.sum_bool]
  cases bit i x <;> simp <;> ring

/-- The identity matrix acts trivially. -/
lemma applyOne_one (i : Fin n) (ψ : Vec n) : applyOne 1 i ψ = ψ := by
  funext x
  simp only [applyOne]
  cases bit i x <;> simp

/-- Gates on distinct qubits commute. -/
lemma applyOne_comm {i j : Fin n} (h : i ≠ j) (A B : Mat1) (ψ : Vec n) :
    applyOne A i (applyOne B j ψ) = applyOne B j (applyOne A i ψ) := by
  funext x
  simp only [applyOne, bit_flipBit_of_ne h, bit_flipBit_of_ne h.symm]
  rw [flipBit_comm i j]
  ring

/-- A single-qubit gate commutes with a CNOT touching neither of its qubits. -/
lemma applyOne_applyCNOT_comm {i c t : Fin n} (hc : i ≠ c) (ht : i ≠ t) (A : Mat1)
    (ψ : Vec n) : applyOne A i (applyCNOT c t ψ) = applyCNOT c t (applyOne A i ψ) := by
  funext x
  simp only [applyOne, applyCNOT, bit_flipBit_of_ne hc.symm, bit_flipBit_of_ne ht]
  split_ifs <;> first | rfl | rw [flipBit_comm i t]

/-- CNOT is an involution. -/
lemma applyCNOT_applyCNOT_self {c t : Fin n} (h : c ≠ t) (ψ : Vec n) :
    applyCNOT c t (applyCNOT c t ψ) = ψ := by
  funext x
  simp only [applyCNOT, bit_flipBit_of_ne h, flipBit_flipBit_self]
  split_ifs <;> rfl

/-- CNOTs commute when neither control is the other gate's target.
They may share a control or share a target. -/
lemma applyCNOT_comm {a b c d : Fin n} (had : a ≠ d) (hcb : c ≠ b) (ψ : Vec n) :
    applyCNOT a b (applyCNOT c d ψ) = applyCNOT c d (applyCNOT a b ψ) := by
  funext x
  simp only [applyCNOT, bit_flipBit_of_ne had, bit_flipBit_of_ne hcb]
  split_ifs <;> first | rfl | rw [flipBit_comm b d]

/-- `X` on the target commutes with a CNOT: both flip the target, and flips
commute. -/
lemma applyCNOT_applyOne_X_target_comm {c t : Fin n} (hct : c ≠ t) (ψ : Vec n) :
    applyCNOT c t (applyOne Gate1.X.mat t ψ) = applyOne Gate1.X.mat t (applyCNOT c t ψ) := by
  funext x
  simp only [applyOne, applyCNOT, Gate1.mat, Matrix.of_apply, bit_flipBit_of_ne hct,
    flipBit_flipBit_self]
  cases bit c x <;> cases bit t x <;> simp

/-- Moving Hadamards on both wires across a CNOT reverses its direction. -/
lemma applyHadamards_applyCNOT {c t : Fin n} (h : c ≠ t) (ψ : Vec n) :
    applyOne Gate1.H.mat t (applyOne Gate1.H.mat c (applyCNOT c t ψ)) =
      applyCNOT t c (applyOne Gate1.H.mat t (applyOne Gate1.H.mat c ψ)) := by
  funext x
  simp only [applyOne, applyCNOT, bit_flipBit_self, bit_flipBit_of_ne h,
    bit_flipBit_of_ne h.symm, flipBit_flipBit_self, flipBit_comm t c]
  cases bit c x <;> cases bit t x <;> simp [Gate1.mat] <;> ring

end Quantum.Circuit
