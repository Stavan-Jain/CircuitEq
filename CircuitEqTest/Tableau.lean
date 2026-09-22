/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tableau

/-!
# Tests of the Clifford tableau checker

Each equivalence is closed by the checker; `decide +kernel` evaluates the
tableau comparison and the soundness theorem turns the `true` into `≡ₛ`.
-/

namespace Quantum.Circuit.Tableau.Tests

open Instr

/-- Conjugating a CNOT by `H ⊗ H` reverses it. -/
theorem hh_cnot_hh : ([H 0, H 1, CX 0 1, H 0, H 1] : Circuit 2) ≡ₛ [CX 1 0] :=
  (tableauChecker 2).sound _ _ (by decide +kernel)

/-- The two three-CNOT decompositions of SWAP agree. -/
theorem swap_swap : ([CX 0 1, CX 1 0, CX 0 1] : Circuit 2) ≡ₛ [CX 1 0, CX 0 1, CX 1 0] :=
  (tableauChecker 2).sound _ _ (by decide +kernel)

/-- CZ is symmetric in its two qubits. -/
theorem cz_symm : ([H 1, CX 0 1, H 1] : Circuit 2) ≡ₛ [H 0, CX 1 0, H 0] :=
  (tableauChecker 2).sound _ _ (by decide +kernel)

/-- `S X S† = Y`; as a circuit, `S†` runs first. -/
theorem Sdg_X_S_eq_Y : ([Sdg 0, X 0, S 0] : Circuit 1) ≡ₛ [Y 0] :=
  (tableauChecker 1).sound _ _ (by decide +kernel)

/-- `Z X = −X Z`: equal up to the scalar `−1`, which the tableau ignores. -/
theorem Z_X_scalar_X_Z : ([Z 0, X 0] : Circuit 1) ≡ₛ [X 0, Z 0] :=
  (tableauChecker 1).sound _ _ (by decide +kernel)

/-- `H` and `S` are not equivalent: the check returns `false`. -/
theorem not_H_S : tableauCheck ([H 0] : Circuit 1) [S 0] = false := by decide +kernel

/-- `T` is outside the fragment: the check is `false` even for equal
circuits. -/
theorem not_T_T : tableauCheck ([T 0] : Circuit 1) [T 0] = false := by decide +kernel

/-- The witness for `[H 0]` versus `[S 0]` is the first generator, `X_0`:
`H` sends it to `Z_0`, `S` to `Y_0`. -/
theorem witness_H_S : witness ([H 0] : Circuit 1) [S 0] = some ⟨1, 0, 0⟩ := by decide +kernel

/-- The tableau of `H 0; CX 0 1`: `X_0 ↦ Z_0`, `X_1 ↦ X_1`, `Z_0 ↦ X_0 X_1`,
`Z_1 ↦ Z_0 Z_1`. -/
theorem tableau_H_CX : tableau ([H 0, CX 0 1] : Circuit 2) =
    some [⟨0, 1, 0⟩, ⟨2, 0, 0⟩, ⟨3, 0, 0⟩, ⟨0, 3, 0⟩] := by
  decide +kernel

/-- The three-qubit phase-flip repetition encoder of
`CircuitEq.Benchmarks.Rep3PhaseFlip` (copied here, so that the tests do not
depend on a benchmark module the harness holds out). -/
def rep3Original : Circuit 3 := [CX 0 1, CX 0 2, H 0, H 1, H 2]

/-- Its PyZX output. -/
def rep3Optimized : Circuit 3 := [CX 0 1, H 1, CX 0 2, H 2, H 0]

/-- The benchmark pair, decided by the tableau. -/
theorem rep3 : rep3Original ≡ₛ rep3Optimized :=
  (tableauChecker 3).sound _ _ (by decide +kernel)

/-- The Steane plus-state encoder of `CircuitEq.Benchmarks.SteanePlus`. -/
def steaneOriginal : Circuit 7 :=
  [H 0, H 1, H 3,
    CX 0 2, CX 0 4, CX 0 6, CX 1 2, CX 1 5, CX 1 6, CX 3 4, CX 3 5, CX 3 6,
    H 0, H 1, H 2, H 3, H 4, H 5, H 6]

/-- Its PyZX output. -/
def steaneOptimized : Circuit 7 :=
  [H 2, CX 2 1, CX 2 0, H 4, CX 4 3, CX 4 0,
    H 5, CX 5 3, CX 5 1, H 6, CX 6 3, CX 6 1, CX 6 0]

/-- The benchmark pair, decided by the tableau on seven qubits. -/
theorem steane : steaneOriginal ≡ₛ steaneOptimized :=
  (tableauChecker 7).sound _ _ (by decide +kernel)

/-! The same pair by the chunked check (`CircuitEq.Chunk`): the seven `X`
generators in one declaration, the seven `Z` generators in another, and a
constant-size term to assemble them. At this size nothing is gained; the
40- and 80-qubit rungs of `benchmarks/scale/` need it. -/

/-- The `X` generators of the Steane pair agree. -/
theorem steane_x :
    (List.range' 0 7).all (tableauCheckGen steaneOriginal steaneOptimized) = true := by
  decide +kernel

/-- The `Z` generators of the Steane pair agree. -/
theorem steane_z :
    (List.range' 7 7).all (tableauCheckGen steaneOriginal steaneOptimized) = true := by
  decide +kernel

/-- The benchmark pair again, assembled from the two chunks. -/
theorem steane_chunked : steaneOriginal ≡ₛ steaneOptimized :=
  tableau_sound_of_allBelow (((AllBelow.zero _).add steane_x).add steane_z)

/-- A generator on which `[H 0]` and `[S 0]` differ: the chunked form of a
rejection. -/
theorem not_H_S_gen : tableauCheckGen ([H 0] : Circuit 1) [S 0] 0 = false := by decide +kernel

end Quantum.Circuit.Tableau.Tests
