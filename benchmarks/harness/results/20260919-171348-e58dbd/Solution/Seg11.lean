import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a11 : Circuit 8 :=
  [Tdg 1, Sdg 2, CX 0 4, CX 3 6, CX 3 5, T 1, CX 7 0, T 0, H 1, Tdg 7, CX 3 6,
    CX 4 3, CX 6 1, Tdg 5, Sdg 7, Y 6, T 6, S 3, T 4, H 2, CX 4 6, CX 1 5, H 2,
    CX 4 2, H 7, CX 2 7, CX 1 6, T 3, T 3, T 7, H 3, CX 1 7, Sdg 0, CX 6 3, H 2,
    Tdg 2, Tdg 1, X 6, CX 3 5, S 6, H 2, CX 2 7, T 4, CX 4 1, S 0, CX 1 4, H 7,
    CX 0 7, Z 5, CX 2 5, Z 1, Z 3, S 6, CX 3 6, X 2, Sdg 4, S 1, Sdg 6, Tdg 3,
    CX 2 5, Tdg 3, Z 4, Sdg 6, H 7, CX 2 1, T 7, S 7, CX 5 1, CX 0 6, H 7,
    CX 2 4, T 6, T 3, CX 1 2, X 7, CX 2 1, Z 4, T 1, Y 6, CX 6 7, T 4, H 5, T 0,
    T 7, CX 4 7, S 2, Tdg 4, CX 5 3, H 0, T 1, CX 0 7, X 5, X 0, Tdg 1, T 1,
    Z 7, H 0, X 5]

def b11 : Circuit 8 :=
  [Sdg 2, CX 0 4, CX 3 5, CX 7 0, H 1, Tdg 7, CX 4 3, CX 6 1, Tdg 5, Sdg 7,
    Y 6, T 6, CX 4 6, CX 1 5, CX 4 2, H 7, CX 2 7, CX 1 6, Z 3, T 7, H 3,
    CX 1 7, CX 6 3, H 2, Tdg 2, Tdg 1, X 6, CX 3 5, H 2, CX 2 7, S 4, CX 4 1,
    CX 1 4, H 7, CX 0 7, Z 5, CX 2 5, Z 3, Z 6, CX 3 6, X 2, Sdg 1, CX 2 5, S 4,
    Z 6, H 7, CX 2 1, T 7, S 7, CX 5 1, CX 0 6, H 7, CX 2 4, T 6, Tdg 3, CX 1 2,
    X 7, CX 2 1, Z 4, Y 6, CX 6 7, H 5, S 0, T 7, CX 4 7, S 2, CX 5 3, H 0,
    CX 0 7, X 0, S 1, Z 7, H 0]

theorem s11 : a11 ≡ᵤ b11 := by
  circuit_windows
    [([CX 3 6, CX 3 6, H 2, H 2],
        []),
      ([T 4, T 4],
        [S 4]),
      ([Tdg 1, T 1, T 0, Sdg 0, S 0, T 0],
        [S 0]),
      ([S 3, T 3, T 3],
        [Z 3]),
      ([S 6, S 6],
        [Z 6]),
      ([Z 1, S 1],
        [Sdg 1]),
      ([Sdg 4, Z 4],
        [S 4]),
      ([Sdg 6, Tdg 3, Sdg 6, T 3],
        [Z 6]),
      ([T 4, Tdg 4],
        []),
      ([T 1, T 1, Tdg 1, T 1],
        [S 1]),
      ([X 5, X 5],
        [])]

end Quantum.Circuit.Harness.Seg
