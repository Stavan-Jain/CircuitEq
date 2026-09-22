import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a5 : Circuit 8 :=
  [Tdg 3, Y 7, Tdg 6, X 4, S 7, Tdg 3, H 0, Tdg 6, Y 5, Z 1, T 3, Tdg 4,
    Tdg 6, S 2, Tdg 6, Sdg 2, Sdg 0, H 4, Sdg 6, Z 4, CX 4 3, CX 0 2, T 6,
    CX 1 5, T 2, T 2, S 6, Tdg 4, Tdg 3, T 3, X 4, CX 5 3, T 0, CX 4 2, Tdg 3,
    H 6, CX 4 6, Tdg 3, CX 3 6, Tdg 6, H 6, X 3, Sdg 3, CX 2 6, Y 7, Tdg 2,
    Tdg 4, T 2, CX 2 5, T 4, S 3, CX 3 5, S 1, CX 6 2, T 1, Y 0, CX 0 6, CX 0 3,
    S 7, H 4, CX 2 0, CX 3 7, T 2, Y 3, Z 7, T 6, CX 4 2, T 1]

def b5 : Circuit 8 :=
  [Y 7, X 4, S 7, H 0, Y 5, Tdg 3, Tdg 4, H 4, Z 4, CX 4 3, CX 0 2, T 6,
    CX 1 5, S 2, Z 6, Tdg 4, X 4, CX 5 3, Tdg 0, CX 4 2, H 6, CX 4 6, Sdg 3,
    CX 3 6, Tdg 6, H 6, X 3, CX 2 6, Y 7, CX 2 5, CX 3 5, CX 6 2, Y 0, CX 0 6,
    CX 0 3, S 7, H 4, CX 2 0, CX 3 7, T 2, Y 3, Z 7, T 6, CX 4 2]

theorem s5 : a5 ≡ᵤ b5 := by
  circuit_windows
    [([Tdg 3, T 3],
        []),
      ([Z 1, S 2, Sdg 2, Sdg 0, CX 0 2, T 2, T 2, T 0, S 1, T 1, Y 0, T 1],
        [CX 0 2, S 2, Tdg 0, Y 0]),
      ([Tdg 3, T 3],
        []),
      ([Tdg 6, Tdg 6, Tdg 6, Tdg 6, Sdg 6, S 6, CX 5 3, Tdg 3, Tdg 3],
        [Z 6, CX 5 3, Sdg 3]),
      ([Tdg 2, T 2],
        []),
      ([Sdg 3, Tdg 4, T 4, S 3],
        [])]

end Quantum.Circuit.Harness.Seg
