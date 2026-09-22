import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a7 : Circuit 8 :=
  [X 6, Y 7, CX 7 4, Y 0, X 4, S 3, H 5, CX 5 1, T 0, H 5, H 5, H 5, S 0, T 2,
    H 5, Sdg 1, T 4, T 5, X 6, Sdg 1, X 0, CX 7 4, Z 4, Sdg 5, H 5, H 7, Tdg 5,
    T 2, CX 4 5, CX 2 0, CX 6 5, Tdg 1, Y 4, S 3, CX 1 6, CX 3 5, Z 6, CX 5 6,
    T 4, CX 3 4, T 3, H 5, T 3, Sdg 1, Sdg 4, H 0, S 6, T 7, CX 6 0, H 7,
    CX 4 5, S 0, T 4, T 5, Y 4, T 6, Tdg 4, T 2, T 2, T 2, CX 0 3, S 0, H 6,
    CX 0 7, X 0, H 7, CX 5 7, S 7, Sdg 6, T 1, T 2, H 0, Y 4, H 2, Tdg 4, X 6,
    CX 4 5, H 4, H 7, CX 7 3, S 1]

def b7 : Circuit 8 :=
  [Y 7, CX 7 4, Y 0, X 4, H 5, CX 5 1, T 0, S 0, T 4, X 0, CX 7 4, Z 4, Tdg 5,
    H 5, H 7, Tdg 5, CX 4 5, CX 2 0, CX 6 5, Y 4, CX 1 6, CX 3 5, Z 6, CX 5 6,
    T 4, CX 3 4, H 5, Sdg 3, H 0, S 6, T 7, CX 6 0, H 7, CX 4 5, Tdg 4, T 5,
    Y 4, T 6, Tdg 4, CX 0 3, Z 0, H 6, CX 0 7, X 0, H 7, CX 5 7, S 7, Sdg 6,
    Sdg 2, H 0, Y 4, H 2, Tdg 4, X 6, CX 4 5, H 4, H 7, CX 7 3, Z 1]

theorem s7 : a7 ≡ᵤ b7 := by
  circuit_windows
    [([S 3, T 2, T 2, S 3, T 3, T 3, T 2, T 2, T 2, T 2],
        [Sdg 3, Sdg 2]),
      ([X 6, X 6],
        []),
      ([Sdg 1, Sdg 1, Tdg 1, Sdg 1, T 1, S 1],
        [Z 1]),
      ([H 5, H 5, H 5, H 5, T 5, Sdg 5, H 5],
        [Tdg 5, H 5]),
      ([Sdg 4, T 4],
        [Tdg 4]),
      ([S 0, S 0],
        [Z 0])]

end Quantum.Circuit.Harness.Seg
