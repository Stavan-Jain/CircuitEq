import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a1 : Circuit 8 :=
  [Tdg 3, CX 0 6, H 0, S 4, S 3, Tdg 1, X 0, CX 0 3, S 6, S 3, Sdg 7, T 5,
    CX 3 6, T 4, X 6, Z 1, CX 4 0, S 6, T 3, H 7, Z 6, Tdg 0, T 6, H 2, H 5,
    CX 1 6, CX 6 2, T 0, T 4, S 6, Tdg 2, T 0, Sdg 3, H 5, Y 5, T 4, Tdg 0, H 2,
    T 3, H 0, T 5, T 3, X 6, T 5, H 0, T 5, T 0, Sdg 2, T 2, Z 4, CX 1 0, Z 7,
    CX 4 1, CX 2 7, CX 2 1, CX 2 5, CX 4 3, S 7, T 0, H 5, H 3, CX 4 5, T 3,
    Y 6, Sdg 0, CX 6 1, CX 2 3, S 6, T 3, Y 7, CX 0 3, Tdg 5, Tdg 6, CX 4 1,
    Y 0, H 1, H 4, S 6, T 2, CX 0 4, Sdg 7, CX 0 3, CX 1 7, T 6]

def b1 : Circuit 8 :=
  [CX 0 6, H 0, T 3, Tdg 1, X 0, CX 0 3, S 6, Sdg 7, T 5, CX 3 6, X 6, Z 1,
    CX 4 0, H 7, Tdg 6, H 2, CX 1 6, CX 6 2, S 6, Tdg 2, Y 5, T 4, H 2, S 3,
    T 3, X 6, S 5, T 5, T 0, CX 1 0, Z 7, CX 2 7, CX 2 1, CX 2 5, CX 4 3, S 7,
    H 5, H 3, CX 4 5, T 3, Y 6, Tdg 0, CX 6 1, CX 2 3, T 3, Y 7, CX 0 3, Tdg 5,
    Y 0, H 1, H 4, CX 0 4, Sdg 7, CX 0 3, CX 1 7, Z 6]

theorem s1 : a1 ≡ᵤ b1 := by
  circuit_windows
    [([Tdg 3, S 3],
        [T 3]),
      ([S 4, T 4, Sdg 3, T 4, T 3, T 3, Z 4],
        []),
      ([H 5, H 5],
        []),
      ([S 6, Z 6, T 6],
        [Tdg 6]),
      ([T 5, T 5],
        [S 5]),
      ([Sdg 2, T 2, T 2],
        []),
      ([Tdg 0, T 0, Tdg 0, H 0, H 0, T 0, CX 1 0, CX 2 1, T 0, Sdg 0],
        [CX 1 0, CX 2 1, Tdg 0]),
      ([CX 4 1, CX 4 1],
        []),
      ([S 6, Tdg 6, S 6, T 6],
        [Z 6])]

end Quantum.Circuit.Harness.Seg
