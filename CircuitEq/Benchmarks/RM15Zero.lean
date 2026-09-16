/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tableau

/-!
# `[[15,1,3]]` Reed–Muller logical zero encoder: original versus PyZX

QECUnitaryCircuits commit `3d96b5fe14a393f8eeefe02f45e5d23916b85a4d`,
`qec_circuits/rm15_1531_encode_0L.qasm`, optimized with PyZX 0.9.0
`full_reduce`. See `benchmarks/rm15_zero/` for the input, output, and
reproduction steps.

The original has 32 gates (4 Hadamards, 28 CNOTs); PyZX re-synthesises it
into 28 (4 Hadamards, 24 CNOTs) with a different CNOT network, so neither
a window alignment nor a block template applies. Both circuits are
Clifford, so the tableau checker of `CircuitEq.Tableau` decides the pair
regardless of structure: `tableauCheck` compares the images of the 30 Pauli
generators, about 0.3 s of kernel time, and `tableauChecker.sound` turns
the `true` into `≡ₛ`, equivalence up to a unit scalar, which is what a
tableau certifies.
-/

namespace Quantum.Circuit.Benchmarks.RM15Zero

open Instr

/-- The original QECUnitaryCircuits encoder, in QASM instruction order. -/
def original : Circuit 15 :=
  [H 7, H 3, H 1, H 0,
    CX 7 8, CX 7 9, CX 7 10, CX 7 11, CX 7 12, CX 7 13, CX 7 14,
    CX 3 4, CX 3 5, CX 3 6, CX 3 11, CX 3 12, CX 3 13, CX 3 14,
    CX 1 2, CX 1 5, CX 1 6, CX 1 9, CX 1 10, CX 1 13, CX 1 14,
    CX 0 2, CX 0 4, CX 0 6, CX 0 8, CX 0 10, CX 0 12, CX 0 14]

/-- The actual PyZX output, in QASM instruction order. -/
def optimized : Circuit 15 :=
  [H 0, H 1, H 3, CX 3 4, CX 0 4, CX 1 5, CX 3 5, CX 3 6, H 7, CX 7 8, CX 0 8, CX 7 9, CX 1 9,
    CX 7 10, CX 0 12, CX 1 13, CX 0 1, CX 1 2, CX 1 6, CX 3 7, CX 1 10, CX 7 11, CX 7 12, CX 7 13,
    CX 7 14, CX 1 14, CX 0 1, CX 3 7]

/-- The original and the PyZX output are equivalent up to a unit scalar:
their Clifford tableaux agree, and the checker is sound. -/
theorem original_equiv_optimized : original ≡ₛ optimized :=
  (tableauChecker 15).sound _ _ (by decide +kernel)

end Quantum.Circuit.Benchmarks.RM15Zero
