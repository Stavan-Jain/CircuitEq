/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.PhasePoly.Complete

/-!
# Tests of the phase-polynomial checker

Each is a theorem proved by the checker: the kernel runs `nf` on both sides
and compares the forms. None enumerates a basis. `decide +kernel` is the
form to use; bare `decide` also closes windows this small, but the
elaborator's evaluator hits the default heartbeat limit at about a hundred
gates on ten wires, where the kernel needs a fraction of a second.
-/

namespace Quantum.Circuit.PhasePoly.Tests

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

end Quantum.Circuit.PhasePoly.Tests
