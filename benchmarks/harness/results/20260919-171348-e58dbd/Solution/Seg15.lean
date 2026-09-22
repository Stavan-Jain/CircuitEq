import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a15 : Circuit 8 :=
  [Sdg 5, H 7, Sdg 6, Z 6, CX 3 6, Z 5, X 1, CX 6 2, T 5, S 5, H 5, H 6, Y 0,
    H 4, CX 2 6, T 2, CX 2 1, CX 4 1, H 5, CX 7 2, CX 2 4, H 7, X 2, S 1, S 7,
    T 0, S 3, Tdg 5, T 5, Z 5, H 1, CX 6 0, Y 3, CX 4 2, T 3, H 0, CX 4 5, T 3,
    CX 2 1, H 4, CX 3 0, H 6, Z 7, Tdg 7, CX 5 1, H 1, CX 3 6, CX 3 0, CX 5 1,
    CX 5 0, Tdg 3, CX 3 4, H 0, CX 7 4, CX 0 6, H 5, CX 1 4, H 4, Tdg 1, T 6,
    Z 4, CX 5 0, Y 5, CX 4 6, Sdg 4, Y 6, Y 4, CX 4 0, CX 6 4, CX 5 6, Tdg 7]

def b15 : Circuit 8 :=
  [H 7, S 6, CX 3 6, X 1, CX 6 2, T 5, H 6, Y 0, H 4, CX 2 6, T 2, CX 2 1,
    CX 4 1, CX 7 2, CX 2 4, H 7, X 2, S 1, T 0, S 3, H 1, CX 6 0, Y 3, CX 4 2,
    H 0, CX 4 5, CX 2 1, H 4, H 6, CX 5 1, H 1, CX 3 6, CX 5 1, CX 5 0, T 3,
    CX 3 4, H 0, CX 7 4, CX 0 6, H 5, CX 1 4, H 4, Tdg 1, T 6, CX 5 0, Y 5,
    CX 4 6, S 4, Y 6, Y 4, CX 4 0, CX 6 4, CX 5 6, Z 7]

theorem s15 : a15 ≡ᵤ b15 := by
  circuit_windows
    [([Sdg 5, S 5],
        []),
      ([Sdg 6, Z 6, Z 5, T 5, H 5, H 5, Tdg 5, T 5, Z 5],
        [S 6, T 5]),
      ([S 7, Tdg 7, Tdg 7],
        []),
      ([T 3, Tdg 3],
        []),
      ([CX 3 0, CX 3 0],
        []),
      ([Z 4, Sdg 4],
        [S 4])]

end Quantum.Circuit.Harness.Seg
