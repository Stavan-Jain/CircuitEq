import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a14 : Circuit 8 :=
  [Sdg 4, Y 5, CX 2 6, Sdg 5, H 6, H 7, Sdg 1, X 6, X 0, Tdg 3, CX 6 3,
    CX 2 5, Y 5, CX 4 3, T 2, CX 5 3, T 7, H 1, Tdg 4, Sdg 4, H 4, S 7, CX 3 6,
    Tdg 4, H 3, CX 2 1, CX 0 7, CX 0 3, S 0, CX 0 7, T 5, Sdg 0, T 7, CX 4 7,
    T 4, X 2, CX 0 1, Y 7, CX 5 3, CX 2 4, Tdg 2, CX 2 7, X 1, CX 5 7, CX 7 1,
    CX 4 2, CX 1 3, CX 3 5, CX 0 1, CX 1 0, Y 3, X 4, T 3, S 4]

def b14 : Circuit 8 :=
  [Y 5, CX 2 6, Sdg 5, H 6, H 7, Sdg 1, X 6, X 0, Tdg 3, CX 6 3, CX 2 5, Y 5,
    CX 4 3, T 2, CX 5 3, H 1, Tdg 4, Z 4, H 4, CX 3 6, H 3, CX 2 1, CX 0 3, T 5,
    Z 7, CX 4 7, X 2, CX 0 1, Y 7, CX 5 3, CX 2 4, Tdg 2, CX 2 7, X 1, CX 5 7,
    CX 7 1, CX 4 2, CX 1 3, CX 3 5, CX 0 1, CX 1 0, Y 3, X 4, T 3, S 4]

theorem s14 : a14 ≡ᵤ b14 := by
  circuit_windows
    [([Sdg 4, Sdg 4],
        [Z 4]),
      ([S 0, Sdg 0],
        []),
      ([T 7, S 7, CX 0 7, CX 0 7, T 7],
        [Z 7]),
      ([Tdg 4, T 4],
        [])]

end Quantum.Circuit.Harness.Seg
