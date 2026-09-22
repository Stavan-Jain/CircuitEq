import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a9 : Circuit 8 :=
  [T 6, S 4, Z 3, Sdg 5, Z 1, CX 5 7, CX 7 2, S 1, CX 4 2, S 6, CX 4 1, H 0,
    T 2, X 4, CX 4 2, T 7, H 7, CX 2 4, S 7, T 0, T 2, Tdg 3, H 7, T 1, CX 2 5,
    CX 1 5, T 0, T 1, CX 3 4, T 4, H 0, Sdg 4, Z 3, CX 3 2, S 5, CX 6 0, CX 5 1,
    CX 2 5, T 5, CX 1 2, H 4, T 5, CX 2 3, H 3, CX 5 2, CX 5 0, H 2, Tdg 4, H 7,
    T 6, H 3, Tdg 2, CX 1 7, CX 6 2, T 4, T 4, T 6, S 5, CX 5 4, T 0, Tdg 7,
    S 2, CX 2 5, Z 3, T 5, H 4, CX 6 7, H 1, Y 2, CX 0 4, Y 2, H 1, T 6, Tdg 6,
    CX 5 3, H 7, CX 7 6, CX 0 6, CX 1 4, CX 5 4, CX 5 6, T 3, X 3, CX 5 6,
    CX 0 5, H 5, CX 0 4, H 6, H 5, T 3, Tdg 2, CX 1 4, CX 7 2, S 1, Y 0, T 3,
    H 2, H 3, CX 5 2, Tdg 7, S 5, T 3, H 6, T 7]

def b9 : Circuit 8 :=
  [S 4, Sdg 5, CX 5 7, CX 7 2, Sdg 1, CX 4 2, CX 4 1, H 0, T 2, X 4, CX 4 2,
    T 7, H 7, CX 2 4, S 7, T 2, Tdg 3, CX 2 5, CX 1 5, S 0, S 1, CX 3 4, H 0,
    Tdg 4, CX 3 2, S 5, CX 6 0, CX 5 1, CX 2 5, CX 1 2, H 4, CX 2 3, CX 5 2,
    CX 5 0, H 2, Z 6, Tdg 2, CX 1 7, CX 6 2, T 4, Z 5, CX 5 4, T 0, Tdg 7,
    CX 2 5, Z 3, T 5, H 4, CX 6 7, T 6, CX 5 3, H 7, CX 7 6, CX 0 6, CX 5 4,
    T 3, X 3, CX 0 5, T 2, CX 7 2, S 1, Y 0, S 3, H 2, H 3, CX 5 2, S 5, T 3]

theorem s9 : a9 ≡ᵤ b9 := by
  circuit_windows
    [([Z 3, Z 3], []),
      ([Z 1, S 1], [Sdg 1]),
      ([H 7, H 7], []),
      ([T 0, T 0], [S 0]),
      ([T 1, T 1], [S 1]),
      ([T 4, Sdg 4], [Tdg 4]),
      ([H 3, H 3], []),
      ([T 6, S 6, T 6], [Z 6]),
      ([Tdg 4, T 4, T 4], [T 4]),
      ([T 5, T 5, S 5], [Z 5]),
      ([S 2, CX 2 5, Y 2, Y 2, Tdg 2], [CX 2 5, T 2]),
      ([T 6, T 6, Tdg 6], [T 6]),
      ([H 1, H 1], []),
      ([CX 5 6, CX 5 6], []),
      ([CX 0 4, CX 0 4], []),
      ([CX 1 4, CX 1 4], []),
      ([H 5, H 5], []),
      ([H 6, H 6], []),
      ([Tdg 7, T 7], []),
      ([T 3, T 3], [S 3])]

end Quantum.Circuit.Harness.Seg
