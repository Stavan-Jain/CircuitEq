import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a13 : Circuit 8 :=
  [CX 0 7, CX 1 4, Sdg 0, X 3, CX 4 1, T 5, H 1, CX 2 1, S 4, Y 6, Tdg 5,
    CX 0 7, Tdg 6, Z 5, H 6, CX 7 6, Z 7, Tdg 7, Tdg 2, Z 4, T 6, Tdg 4, CX 0 4,
    S 7, T 5, CX 7 1, S 5, S 2, H 6, CX 1 2, Z 0, CX 0 2, H 5, H 0, CX 1 2,
    CX 1 7]

def b13 : Circuit 8 :=
  [CX 1 4, X 3, CX 4 1, H 1, CX 2 1, Y 6, Tdg 6, H 6, CX 7 6, Tdg 7, Sdg 4,
    T 6, Tdg 4, CX 0 4, Sdg 7, CX 7 1, Tdg 5, T 2, H 6, S 0, CX 0 2, H 5, H 0,
    CX 1 7]

theorem s13 : a13 ≡ᵤ b13 := by
  circuit_windows
    [([CX 0 7, Sdg 0, CX 0 7, Z 0],
        [S 0]),
      ([Tdg 2, S 2],
        [T 2]),
      ([Z 7, S 7],
        [Sdg 7]),
      ([T 5, Z 5, T 5, S 5],
        []),
      ([S 4, Z 4],
        [Sdg 4]),
      ([CX 1 2, CX 1 2],
        [])]

end Quantum.Circuit.Harness.Seg
