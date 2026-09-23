import Solution.Finish
set_option Elab.async false
set_option maxRecDepth 50000
namespace Quantum.Circuit.Harness
open Instr

/-- The common intervening Hadamards and linear network. -/
def bridge : Circuit 48 :=
  [H 32, H 33, H 34, H 35, H 36, H 37, H 38, H 39, H 40, H 41, H 42, H 43, H 44, H 45, H 46, CX 46 35, CX 46 33, CX 46 32, CX 45 34, CX 45 32, CX 45 47, CX 44 33, CX 44 47, CX 44 46, CX 43 32, CX 43 46, CX 43 45, CX 42 47, CX 42 45, CX 42 44, CX 41 46, CX 41 44, CX 41 43, CX 40 45, CX 40 43, CX 40 42, CX 39 44, CX 39 42, CX 39 41, CX 38 43, CX 38 41, CX 38 40, CX 37 42, CX 37 40, CX 37 39, CX 36 41, CX 36 39, CX 36 38, CX 35 40, CX 35 38, CX 35 37, CX 34 39, CX 34 37, CX 34 36, CX 33 38, CX 33 36, CX 33 35, CX 32 37, CX 32 35, CX 32 34]

/-- Gather the optimized circuit's disjoint Hadamards at each block boundary. -/
theorem optimized_normal : optimized ≡ᵤ h0 ++ e0 ++ middle ++ e1 ++ h1 := by
  exact ((gather0.append (Equivalent.refl bridge)).append gather1).append
    (Equivalent.refl h1)

/-- The two circuits have exactly the same unitary, hence the claimed phase relation. -/
theorem equiv : original ≡ₚ optimized :=
  (original_normal.trans (between_normal.trans optimized_normal.symm)).toUpToPhase

end Quantum.Circuit.Harness
