import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a2 : Circuit 8 :=
  [Tdg 7, CX 6 2, T 0, H 6, X 0, CX 5 6, Y 2, H 3, CX 1 6, H 5, X 7, Sdg 3,
    CX 0 7, CX 2 4, CX 5 4, T 4, H 5, CX 3 6, X 7, CX 1 2, CX 1 3, Z 2, Z 5,
    CX 6 0, T 3, T 4, H 4, T 1, T 4, CX 0 6, CX 0 7, H 0, CX 6 1, CX 2 5,
    CX 1 3, X 6, Sdg 4, T 7, H 3, Tdg 0, CX 4 5, Tdg 7, H 6, CX 5 4, Y 1,
    CX 7 5, H 2, T 4, CX 5 0, Sdg 1, Y 7, CX 5 1, H 4, CX 2 7, Sdg 4, CX 1 4,
    Tdg 1, CX 0 6, CX 1 2, T 1]

def b2 : Circuit 8 :=
  [Tdg 7, CX 6 2, T 0, H 6, X 0, CX 5 6, Y 2, H 3, CX 1 6, H 5, Sdg 3, CX 0 7,
    CX 2 4, CX 5 4, H 5, CX 3 6, CX 1 2, CX 1 3, Z 2, Z 5, CX 6 0, T 3, S 4,
    H 4, T 1, CX 0 6, CX 0 7, H 0, CX 6 1, CX 2 5, CX 1 3, X 6, Tdg 4, H 3,
    Tdg 0, CX 4 5, H 6, CX 5 4, Y 1, CX 7 5, H 2, T 4, CX 5 0, Sdg 1, Y 7,
    CX 5 1, H 4, CX 2 7, Sdg 4, CX 1 4, CX 0 6, CX 1 2]

theorem s2 : a2 ≡ᵤ b2 := by
  circuit_windows
    [([T 4, T 4],
        [S 4]),
      ([T 4, Sdg 4],
        [Tdg 4]),
      ([X 7, X 7, T 7, Tdg 7],
        []),
      ([Tdg 1, T 1],
        [])]

end Quantum.Circuit.Harness.Seg
