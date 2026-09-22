import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a3 : Circuit 8 :=
  [S 0, Tdg 4, S 5, T 2, CX 5 0, T 2, CX 2 1, Z 5, H 4, CX 3 1, T 0, Sdg 3,
    CX 6 4, CX 3 2, Sdg 7, Sdg 4, T 7, CX 5 1, CX 0 6, Tdg 6, Y 0, CX 5 4,
    CX 2 1, CX 4 3, T 2, Tdg 3, T 2, T 7, X 3, CX 7 5, T 3]

def b3 : Circuit 8 :=
  [S 0, Tdg 4, CX 5 0, S 2, CX 2 1, Sdg 5, H 4, CX 3 1, T 0, Sdg 3, CX 6 4,
    CX 3 2, Sdg 4, CX 5 1, CX 0 6, Tdg 6, Y 0, CX 5 4, CX 2 1, CX 4 3, Tdg 3,
    S 2, X 3, CX 7 5, T 3]

theorem s3 : a3 ≡ᵤ b3 := by
  circuit_windows
    [([T 2, T 2],
        [S 2]),
      ([S 5, Z 5],
        [Sdg 5]),
      ([Sdg 7, T 7, T 7],
        []),
      ([T 2, T 2],
        [S 2])]

end Quantum.Circuit.Harness.Seg
