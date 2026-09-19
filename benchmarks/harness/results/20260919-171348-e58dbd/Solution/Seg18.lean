import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a18 : Circuit 8 :=
  [CX 6 2, Tdg 6, H 5, Y 3, CX 2 1, CX 3 5, H 7, T 0, CX 0 7, H 4, H 3, S 5,
    X 5, Tdg 0, T 2, S 5, Tdg 5, CX 3 5, Tdg 6, Y 0, H 2, CX 7 5, CX 1 6, Sdg 6,
    CX 1 7, T 6, Tdg 6, CX 6 3, Z 5, H 1, CX 5 0, CX 1 7, CX 1 0]

def b18 : Circuit 8 :=
  [CX 6 2, H 5, Y 3, CX 2 1, CX 3 5, H 7, CX 0 7, H 4, H 3, S 5, X 5, T 2,
    T 5, CX 3 5, Sdg 6, Y 0, H 2, CX 7 5, CX 1 6, CX 1 7, Sdg 6, CX 6 3, Z 5,
    H 1, CX 5 0, CX 1 7, CX 1 0]

theorem s18 : a18 ≡ᵤ b18 := by
  circuit_windows
    [([T 0, Tdg 0],
        []),
      ([Tdg 6, Tdg 6],
        [Sdg 6]),
      ([S 5, Tdg 5],
        [T 5]),
      ([T 6, Tdg 6],
        [])]

end Quantum.Circuit.Harness.Seg
