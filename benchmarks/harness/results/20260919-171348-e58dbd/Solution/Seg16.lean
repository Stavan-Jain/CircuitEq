import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a16 : Circuit 8 :=
  [T 4, Tdg 5, CX 1 3, H 3, H 7, CX 7 5, CX 3 0, S 0, T 7, T 5, X 2, T 7, H 6,
    T 7, CX 5 0, Z 5, Z 7, CX 4 6, CX 5 1, CX 7 6, CX 5 4, H 2, T 7, CX 3 4,
    CX 2 4, CX 6 3, CX 4 1, Y 5, CX 4 1, T 6, T 4, CX 4 7, Z 3, CX 2 5, CX 5 0,
    H 2, Tdg 7, T 7, H 3, CX 1 0, T 2, T 2, T 0, Tdg 7, T 4, X 2, Z 4, CX 0 4,
    CX 1 4, CX 5 3, H 1, H 7, CX 6 3, H 1, CX 6 4, S 7, T 5, CX 2 4, CX 3 7]

def b16 : Circuit 8 :=
  [T 4, Tdg 5, CX 1 3, H 3, H 7, CX 7 5, CX 3 0, S 0, T 5, X 2, H 6, CX 5 0,
    Z 5, CX 4 6, CX 5 1, CX 7 6, CX 5 4, H 2, CX 3 4, CX 2 4, CX 6 3, Y 5, T 6,
    CX 4 7, Z 3, CX 2 5, CX 5 0, H 2, H 3, CX 1 0, S 2, T 0, Tdg 7, X 2, Sdg 4,
    CX 0 4, CX 1 4, CX 5 3, H 7, CX 6 3, CX 6 4, S 7, T 5, CX 2 4, CX 3 7]

theorem s16 : a16 ≡ᵤ b16 := by
  circuit_windows
    [([T 7, T 7, T 7, Z 7, T 7],
        []),
      ([CX 4 1, CX 4 1],
        []),
      ([T 4, T 4, Z 4],
        [Sdg 4]),
      ([T 2, T 2],
        [S 2]),
      ([T 7, Tdg 7, H 1, H 1],
        [])]

end Quantum.Circuit.Harness.Seg
