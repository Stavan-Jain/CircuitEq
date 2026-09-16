/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import Mathlib.Data.Nat.Bitwise

/-!
# Bit access on computational-basis indices

An `n`-qubit register's computational basis is indexed by `Fin (2 ^ n)`, read
as an `n`-bit string: bit `i` of the index is the state of qubit `i`. This
file provides the two primitives the sparse gate semantics needs — reading a
bit and flipping a bit — together with the handful of rewrite lemmas that
make gates on disjoint qubits commute:

- `bit_flipBit_self`, `bit_flipBit_of_ne` — how `bit` sees a flip;
- `flipBit_flipBit_self`, `flipBit_comm` — flips are involutions and commute.

Everything is phrased through `Nat.testBit` and `Nat.xor`, which the kernel
evaluates with GMP-accelerated arithmetic, so `decide` on concrete indices
is cheap.
-/

namespace Quantum.Circuit

/-- Bit `i` of the basis index `x`: the computational-basis state of qubit
`i`. `false` is `|0⟩`, `true` is `|1⟩`. -/
def bit {n : ℕ} (i : Fin n) (x : Fin (2 ^ n)) : Bool :=
  x.val.testBit i.val

/-- Flip bit `i` of the basis index `x`: the action of `X` on qubit `i` on
basis states. -/
def flipBit {n : ℕ} (i : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ i.val,
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right Nat.one_lt_two i.isLt)⟩

variable {n : ℕ}

@[simp] lemma val_flipBit (i : Fin n) (x : Fin (2 ^ n)) :
    (flipBit i x).val = x.val ^^^ 2 ^ i.val := rfl

@[simp] lemma bit_flipBit_self (i : Fin n) (x : Fin (2 ^ n)) :
    bit i (flipBit i x) = !bit i x := by
  simp [bit, flipBit, Nat.testBit_xor, Nat.testBit_two_pow_self]

@[simp] lemma bit_flipBit_of_ne {i j : Fin n} (h : i ≠ j) (x : Fin (2 ^ n)) :
    bit i (flipBit j x) = bit i x := by
  have hji : j.val ≠ i.val := fun h' => h (Fin.ext h'.symm)
  simp [bit, flipBit, Nat.testBit_xor, Nat.testBit_two_pow_of_ne hji]

@[simp] lemma flipBit_flipBit_self (i : Fin n) (x : Fin (2 ^ n)) :
    flipBit i (flipBit i x) = x := by
  ext
  simp

lemma flipBit_comm (i j : Fin n) (x : Fin (2 ^ n)) :
    flipBit i (flipBit j x) = flipBit j (flipBit i x) := by
  ext
  simp only [val_flipBit]
  rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm (2 ^ j.val)]

end Quantum.Circuit
