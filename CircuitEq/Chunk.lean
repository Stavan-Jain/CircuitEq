/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import Mathlib.Data.List.Range

/-!
# Chunked kernel evaluation

The kernel memoises `whnf` by structural equality of terms and keeps the
cache for the whole of one declaration, releasing it only when the
declaration ends. A long `decide +kernel` is therefore bounded by memory
before it is bounded by time: the seven-qubit basis decide was killed at
6.9 GB after 20 s, and the 40-qubit tableau at 6.3 GB, with arithmetic that
would have finished in under a minute.

The lever is to give the kernel one declaration per *chunk* of the work. A
check that is a conjunction over the indices `0, …, k − 1` (the basis
vectors of `checkEquiv`, the generators of a tableau) is proved one range of
indices at a time, each range a separate theorem closed by its own
`decide +kernel`, and the ranges are assembled by a proof term of constant
size per chunk:

```lean
theorem r0 : (List.range' 0 16).all (checkEquivAt a b) = true := by decide +kernel
theorem r1 : (List.range' 16 16).all (checkEquivAt a b) = true := by decide +kernel
theorem all : AllBelow (checkEquivAt a b) 32 := ((AllBelow.zero _).add r0).add r1
```

Peak memory is that of the largest chunk and total time is unchanged. The
chunk boundaries are data an external tool chooses, in the spirit of the
certificate language; `scripts/scale_test.py --chunk` and
`scripts/chunked_decide.py` emit such files. Consumers:
`equivalent_of_allBelow` and `equivalentUpToPhase_of_allBelow`
(`CircuitEq.Semantics`) and `tableau_sound_of_allBelow`
(`CircuitEq.Tableau`).
-/

namespace Quantum.Circuit

/-- `P` holds at every index below `k`: the state of a chunked check. -/
def AllBelow (P : ℕ → Bool) (k : ℕ) : Prop := ∀ y, y < k → P y = true

namespace AllBelow

/-- Nothing to check below zero. -/
theorem zero (P : ℕ → Bool) : AllBelow P 0 := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Extend a chunked check by the range `lo, …, lo + len − 1`, itself one
kernel evaluation. -/
theorem add {P : ℕ → Bool} {lo len : ℕ} (h : AllBelow P lo)
    (hr : (List.range' lo len).all P = true) : AllBelow P (lo + len) := by
  intro y hy
  by_cases hlo : y < lo
  · exact h y hlo
  · exact List.all_eq_true.1 hr y (List.mem_range'_1.2 ⟨not_lt.1 hlo, hy⟩)

/-- A chunked check is the unchunked one. -/
theorem all_range {P : ℕ → Bool} {k : ℕ} (h : AllBelow P k) : (List.range k).all P = true :=
  List.all_eq_true.2 fun y hy => h y (List.mem_range.1 hy)

end AllBelow

end Quantum.Circuit
