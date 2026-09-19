import CircuitEq
import Harness.Task

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace Quantum.Circuit.Harness

open Instr

def a0 : Circuit 8 :=
  [CX 1 2, CX 7 3]
def b0 : Circuit 8 :=
  [CX 1 2, CX 7 3]
theorem s0 : a0 ≡ᵤ b0 := Equivalent.refl _

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

def a2 : Circuit 8 :=
  [Tdg 7, CX 6 2, T 0, H 6, X 0, CX 5 6, Y 2, H 3, CX 1 6, H 5]
def b2 : Circuit 8 :=
  [Tdg 7, CX 6 2, T 0, H 6, X 0, CX 5 6, Y 2, H 3, CX 1 6, H 5]
theorem s2 : a2 ≡ᵤ b2 := Equivalent.refl _

def a3 : Circuit 8 :=
  [X 7, Sdg 3, CX 0 7, CX 2 4, CX 5 4, T 4, H 5, CX 3 6, X 7, CX 1 2, CX 1 3,
    Z 2, Z 5, CX 6 0, T 3, T 4]
def b3 : Circuit 8 :=
  [Sdg 3, CX 0 7, CX 2 4, CX 5 4, H 5, CX 3 6, CX 1 2, CX 1 3, Z 2, Z 5,
    CX 6 0, T 3, S 4]
theorem s3 : a3 ≡ᵤ b3 := by
  circuit_windows
    [([X 7, X 7],
        []),
      ([T 4, T 4],
        [S 4])]

def a4 : Circuit 8 :=
  [H 4, T 1]
def b4 : Circuit 8 :=
  [H 4, T 1]
theorem s4 : a4 ≡ᵤ b4 := Equivalent.refl _

def a5 : Circuit 8 :=
  [T 4, CX 0 6, CX 0 7, H 0, CX 6 1, CX 2 5, CX 1 3, X 6, Sdg 4]
def b5 : Circuit 8 :=
  [CX 0 6, CX 0 7, H 0, CX 6 1, CX 2 5, CX 1 3, X 6, Tdg 4]
theorem s5 : a5 ≡ᵤ b5 := by
  circuit_windows
    [([T 4, Sdg 4],
        [Tdg 4])]

def a6 : Circuit 8 :=
  [T 7, H 3, Tdg 0, CX 4 5, Tdg 7]
def b6 : Circuit 8 :=
  [H 3, Tdg 0, CX 4 5]
theorem s6 : a6 ≡ᵤ b6 := by
  circuit_windows
    [([T 7, Tdg 7],
        [])]

def a7 : Circuit 8 :=
  [H 6, CX 5 4, Y 1, CX 7 5, H 2, T 4, CX 5 0, Sdg 1, Y 7, CX 5 1, H 4,
    CX 2 7, Sdg 4, CX 1 4]
def b7 : Circuit 8 :=
  [H 6, CX 5 4, Y 1, CX 7 5, H 2, T 4, CX 5 0, Sdg 1, Y 7, CX 5 1, H 4,
    CX 2 7, Sdg 4, CX 1 4]
theorem s7 : a7 ≡ᵤ b7 := Equivalent.refl _

def a8 : Circuit 8 :=
  [Tdg 1, CX 0 6, CX 1 2, T 1]
def b8 : Circuit 8 :=
  [CX 0 6, CX 1 2]
theorem s8 : a8 ≡ᵤ b8 := by
  circuit_windows
    [([Tdg 1, T 1],
        [])]

def a9 : Circuit 8 :=
  [S 0, Tdg 4]
def b9 : Circuit 8 :=
  [S 0, Tdg 4]
theorem s9 : a9 ≡ᵤ b9 := Equivalent.refl _

def a10 : Circuit 8 :=
  [S 5, T 2, CX 5 0, T 2, CX 2 1, Z 5]
def b10 : Circuit 8 :=
  [CX 5 0, S 2, CX 2 1, Sdg 5]
theorem s10 : a10 ≡ᵤ b10 := by
  circuit_windows
    [([S 5, T 2, T 2, Z 5],
        [S 2, Sdg 5])]

def a11 : Circuit 8 :=
  [H 4, CX 3 1, T 0, Sdg 3, CX 6 4, CX 3 2]
def b11 : Circuit 8 :=
  [H 4, CX 3 1, T 0, Sdg 3, CX 6 4, CX 3 2]
theorem s11 : a11 ≡ᵤ b11 := Equivalent.refl _

def a12 : Circuit 8 :=
  [Sdg 7, Sdg 4, T 7, CX 5 1, CX 0 6, Tdg 6, Y 0, CX 5 4, CX 2 1, CX 4 3, T 2,
    Tdg 3, T 2, T 7]
def b12 : Circuit 8 :=
  [Sdg 4, CX 5 1, CX 0 6, Tdg 6, Y 0, CX 5 4, CX 2 1, CX 4 3, Tdg 3, S 2]
theorem s12 : a12 ≡ᵤ b12 := by
  circuit_windows
    [([T 2, T 2],
        [S 2]),
      ([Sdg 7, T 7, T 7],
        [])]

def a13 : Circuit 8 :=
  [X 3, CX 7 5, T 3]
def b13 : Circuit 8 :=
  [X 3, CX 7 5, T 3]
theorem s13 : a13 ≡ᵤ b13 := Equivalent.refl _

def a14 : Circuit 8 :=
  [S 5, T 4, Y 3, CX 1 6, T 5, CX 3 2, CX 4 6, T 2, S 7, Tdg 1, X 6, CX 4 3,
    CX 0 3, S 5, H 2, T 0, T 1, Sdg 1, CX 1 7, Y 1, T 3, Y 6, X 6, H 5, H 7,
    Y 1, H 6, X 4, CX 6 5, T 3, T 0]
def b14 : Circuit 8 :=
  [T 4, Y 3, CX 1 6, T 5, CX 3 2, CX 4 6, T 2, S 7, X 6, CX 4 3, CX 0 3, Z 5,
    H 2, Sdg 1, CX 1 7, Y 6, X 6, H 5, H 7, H 6, X 4, CX 6 5, S 3, S 0]
theorem s14 : a14 ≡ᵤ b14 := by
  circuit_windows
    [([T 0, T 0],
        [S 0]),
      ([Tdg 1, T 1],
        []),
      ([S 5, S 5],
        [Z 5]),
      ([T 3, T 3],
        [S 3]),
      ([Y 1, Y 1],
        [])]

def a15 : Circuit 8 :=
  [CX 3 6, CX 2 7, CX 3 2, H 4]
def b15 : Circuit 8 :=
  [CX 3 6, CX 2 7, CX 3 2, H 4]
theorem s15 : a15 ≡ᵤ b15 := Equivalent.refl _

def a16 : Circuit 8 :=
  [Z 7, Sdg 2, T 7, H 1, Sdg 6, CX 1 6, CX 0 4, CX 2 0, T 4, H 5, S 5, CX 7 5,
    T 4, T 5, Sdg 7]
def b16 : Circuit 8 :=
  [Sdg 2, T 7, H 1, Sdg 6, CX 1 6, CX 0 4, CX 2 0, H 5, S 5, CX 7 5, S 4, T 5,
    S 7]
theorem s16 : a16 ≡ᵤ b16 := by
  circuit_windows
    [([Z 7, Sdg 7],
        [S 7]),
      ([T 4, T 4],
        [S 4])]

def a17 : Circuit 8 :=
  [CX 6 3, CX 0 2]
def b17 : Circuit 8 :=
  [CX 6 3, CX 0 2]
theorem s17 : a17 ≡ᵤ b17 := Equivalent.refl _

def a18 : Circuit 8 :=
  [Tdg 3, Y 7, Tdg 6, X 4, S 7, Tdg 3, H 0, Tdg 6, Y 5, Z 1, T 3, Tdg 4,
    Tdg 6, S 2, Tdg 6, Sdg 2, Sdg 0, H 4, Sdg 6, Z 4, CX 4 3, CX 0 2, T 6,
    CX 1 5, T 2, T 2, S 6, Tdg 4, Tdg 3, T 3, X 4, CX 5 3, T 0, CX 4 2, Tdg 3,
    H 6, CX 4 6, Tdg 3, CX 3 6, Tdg 6, H 6, X 3, Sdg 3, CX 2 6, Y 7, Tdg 2,
    Tdg 4, T 2, CX 2 5, T 4, S 3, CX 3 5, S 1, CX 6 2, T 1, Y 0, CX 0 6, CX 0 3,
    S 7, H 4, CX 2 0, CX 3 7, T 2, Y 3, Z 7, T 6, CX 4 2, T 1]
def b18 : Circuit 8 :=
  [Y 7, X 4, S 7, H 0, Y 5, Tdg 3, Tdg 4, H 4, Z 4, CX 4 3, CX 0 2, T 6,
    CX 1 5, S 2, Z 6, Tdg 4, X 4, CX 5 3, Tdg 0, CX 4 2, H 6, CX 4 6, Sdg 3,
    CX 3 6, Tdg 6, H 6, X 3, CX 2 6, Y 7, CX 2 5, CX 3 5, CX 6 2, Y 0, CX 0 6,
    CX 0 3, S 7, H 4, CX 2 0, CX 3 7, T 2, Y 3, Z 7, T 6, CX 4 2]
theorem s18 : a18 ≡ᵤ b18 := by
  circuit_windows
    [([Tdg 3, Z 1, T 3, S 2, Sdg 2, S 1, T 1, T 1],
        []),
      ([Sdg 6, S 6],
        []),
      ([Tdg 6, Tdg 6, Tdg 6, Tdg 6],
        [Z 6]),
      ([Sdg 0, T 0],
        [Tdg 0]),
      ([T 2, T 2, Tdg 4, Tdg 3, T 3, X 4, CX 5 3, CX 4 2, Tdg 3, H 6, Tdg 3,
        CX 3 6, X 3, Sdg 3, Tdg 2, T 2, S 3, CX 3 5, Y 0, CX 0 3],
        [S 2, Tdg 4, X 4, CX 5 3, CX 4 2, H 6, Sdg 3, CX 3 6, X 3, CX 3 5, Y 0,
        CX 0 3]),
      ([Tdg 4, T 4],
        []),
      ([CX 3 7, Y 3, Z 7],
        [CX 3 7, Y 3, Z 7])]

def a19 : Circuit 8 :=
  [X 1, CX 0 6, T 6, Z 4, X 6, CX 2 6, X 0, H 0, T 4, CX 7 5, Z 0, CX 0 4,
    Z 0, X 1, H 3, CX 2 5, CX 3 5, T 5, Tdg 4, Tdg 3, CX 2 7, H 0, X 6, T 6,
    X 1, S 1, CX 1 7, CX 3 6, H 0, CX 1 6, T 5, CX 5 0, CX 0 3, Tdg 6, Sdg 7,
    CX 4 0, CX 5 0, H 6, CX 4 2, S 4, Sdg 1]
def b19 : Circuit 8 :=
  [CX 0 6, T 6, Z 4, CX 2 6, X 0, H 0, T 4, CX 7 5, CX 0 4, H 3, CX 2 5,
    CX 3 5, Tdg 3, CX 2 7, T 6, X 1, CX 1 7, CX 3 6, CX 1 6, S 5, CX 5 0,
    CX 0 3, Tdg 6, Sdg 7, CX 4 0, CX 5 0, H 6, CX 4 2, T 4]
theorem s19 : a19 ≡ᵤ b19 := by
  circuit_windows
    [([X 6, X 6],
        []),
      ([Z 0, Z 0],
        []),
      ([Tdg 4, H 0, H 0, S 4],
        [T 4]),
      ([T 5, T 5],
        [S 5]),
      ([X 1, X 1, S 1, Sdg 1],
        [])]

def a20 : Circuit 8 :=
  [Z 4, CX 3 4, T 5]
def b20 : Circuit 8 :=
  [Z 4, CX 3 4, T 5]
theorem s20 : a20 ≡ᵤ b20 := Equivalent.refl _

def a21 : Circuit 8 :=
  [X 6, Y 7, CX 7 4, Y 0, X 4, S 3, H 5, CX 5 1, T 0, H 5, H 5, H 5, S 0, T 2,
    H 5, Sdg 1, T 4, T 5, X 6, Sdg 1, X 0, CX 7 4, Z 4, Sdg 5, H 5, H 7, Tdg 5,
    T 2, CX 4 5, CX 2 0, CX 6 5, Tdg 1, Y 4, S 3, CX 1 6, CX 3 5, Z 6, CX 5 6,
    T 4, CX 3 4, T 3, H 5, T 3, Sdg 1, Sdg 4, H 0, S 6, T 7, CX 6 0, H 7,
    CX 4 5, S 0, T 4, T 5, Y 4, T 6, Tdg 4, T 2, T 2, T 2, CX 0 3, S 0, H 6,
    CX 0 7, X 0, H 7, CX 5 7, S 7, Sdg 6, T 1, T 2, H 0, Y 4, H 2, Tdg 4, X 6,
    CX 4 5, H 4, H 7, CX 7 3, S 1]
def b21 : Circuit 8 :=
  [Y 7, CX 7 4, Y 0, X 4, H 5, CX 5 1, T 0, S 0, T 4, X 0, CX 7 4, Z 4, Tdg 5,
    H 5, H 7, Tdg 5, CX 4 5, CX 2 0, CX 6 5, Y 4, CX 1 6, CX 3 5, Z 6, CX 5 6,
    T 4, CX 3 4, H 5, Sdg 3, H 0, S 6, T 7, CX 6 0, H 7, CX 4 5, Tdg 4, T 5,
    Y 4, T 6, Tdg 4, CX 0 3, Z 0, H 6, CX 0 7, X 0, H 7, CX 5 7, S 7, Sdg 6,
    Sdg 2, H 0, Y 4, H 2, Tdg 4, X 6, CX 4 5, H 4, H 7, CX 7 3, Z 1]
theorem s21 : a21 ≡ᵤ b21 := by
  circuit_windows
    [([T 2, T 2, T 2, T 2, T 2, T 2],
        [Sdg 2]),
      ([S 3, S 3, T 3, T 3],
        [Sdg 3]),
      ([X 6, X 6],
        []),
      ([H 5, H 5, H 5, H 5, Sdg 1, T 5, Sdg 1, Sdg 5, Tdg 1, Sdg 1, T 1, S 1],
        [Tdg 5, Z 1]),
      ([Sdg 4, T 4],
        [Tdg 4]),
      ([S 0, S 0],
        [Z 0])]

def a22 : Circuit 8 :=
  [CX 3 1, CX 0 7, CX 7 6, Y 6, Tdg 2, Z 1, H 0, T 6, H 1, S 6, Z 1, Y 4,
    CX 0 6, CX 1 6, H 7, CX 7 3, CX 7 0, CX 3 1]
def b22 : Circuit 8 :=
  [CX 3 1, CX 0 7, CX 7 6, Y 6, Tdg 2, Z 1, H 0, T 6, H 1, S 6, Z 1, Y 4,
    CX 0 6, CX 1 6, H 7, CX 7 3, CX 7 0, CX 3 1]
theorem s22 : a22 ≡ᵤ b22 := Equivalent.refl _

def a23 : Circuit 8 :=
  [T 6, S 4, Z 3, Sdg 5, Z 1, CX 5 7, CX 7 2, S 1, CX 4 2, S 6, CX 4 1, H 0,
    T 2, X 4, CX 4 2, T 7, H 7, CX 2 4, S 7, T 0, T 2, Tdg 3, H 7, T 1, CX 2 5,
    CX 1 5, T 0, T 1, CX 3 4, T 4, H 0, Sdg 4, Z 3, CX 3 2, S 5, CX 6 0, CX 5 1,
    CX 2 5, T 5, CX 1 2, H 4, T 5, CX 2 3, H 3, CX 5 2, CX 5 0, H 2, Tdg 4, H 7,
    T 6, H 3, Tdg 2, CX 1 7, CX 6 2, T 4, T 4, T 6, S 5, CX 5 4, T 0, Tdg 7,
    S 2, CX 2 5, Z 3, T 5, H 4, CX 6 7, H 1, Y 2, CX 0 4, Y 2, H 1, T 6, Tdg 6,
    CX 5 3, H 7, CX 7 6, CX 0 6, CX 1 4, CX 5 4, CX 5 6, T 3, X 3, CX 5 6,
    CX 0 5, H 5, CX 0 4, H 6, H 5, T 3, Tdg 2, CX 1 4, CX 7 2, S 1, Y 0, T 3,
    H 2, H 3, CX 5 2, Tdg 7, S 5, T 3, H 6, T 7]
def b23 : Circuit 8 :=
  [S 4, Sdg 5, CX 5 7, CX 7 2, Sdg 1, CX 4 2, CX 4 1, H 0, T 2, X 4, CX 4 2,
    T 7, H 7, CX 2 4, S 7, T 2, Tdg 3, CX 2 5, CX 1 5, S 0, S 1, CX 3 4, H 0,
    Tdg 4, CX 3 2, S 5, CX 6 0, CX 5 1, CX 2 5, CX 1 2, H 4, CX 2 3, CX 5 2,
    CX 5 0, H 2, Z 6, Tdg 2, CX 1 7, CX 6 2, T 4, Z 5, CX 5 4, T 0, Tdg 7,
    CX 2 5, Z 3, T 5, H 4, CX 6 7, T 6, CX 5 3, H 7, CX 7 6, CX 0 6, CX 5 4,
    T 3, X 3, CX 0 5, T 2, CX 7 2, S 1, Y 0, S 3, H 2, H 3, CX 5 2, S 5, T 3]
theorem s23 : a23 ≡ᵤ b23 := by
  circuit_windows
    [([Z 3, Z 3],
        []),
      ([Z 1, S 1, CX 4 1, T 1, T 1],
        [Sdg 1, CX 4 1, S 1]),
      ([T 0, T 0],
        [S 0]),
      ([H 7, H 7],
        []),
      ([T 4, Sdg 4],
        [Tdg 4]),
      ([Tdg 4, T 4],
        []),
      ([T 6, S 6, T 5, T 5, H 3, T 6, H 3, Tdg 2, CX 1 7, CX 6 2, T 4, T 6,
        S 5, CX 5 4, Tdg 7, S 2, CX 2 5, Z 3, T 5, H 4, CX 6 7, Y 2, CX 0 4,
        Y 2, T 6, Tdg 6, CX 5 3, H 7, CX 7 6, CX 0 6, CX 5 4, CX 5 6, CX 5 6,
        CX 0 5, H 5, CX 0 4, H 5, Tdg 2, S 5],
        [Z 6, Tdg 2, CX 1 7, CX 6 2, T 4, Z 5, CX 5 4, Tdg 7, CX 2 5, Z 3, T 5,
        H 4, CX 6 7, T 6, CX 5 3, H 7, CX 7 6, CX 0 6, CX 5 4, CX 0 5, T 2, S 5]),
      ([H 1, H 1, CX 1 4, CX 1 4],
        []),
      ([H 6, Tdg 7, H 6, T 7],
        []),
      ([T 3, T 3],
        [S 3])]

def a24 : Circuit 8 :=
  [X 2, CX 6 3, CX 0 5, CX 2 3, Sdg 4, X 2, Y 1, X 0, T 3, T 6, Y 3, Y 2,
    Tdg 5]
def b24 : Circuit 8 :=
  [X 2, CX 6 3, CX 0 5, CX 2 3, Sdg 4, X 2, Y 1, X 0, T 3, T 6, Y 3, Y 2,
    Tdg 5]
theorem s24 : a24 ≡ᵤ b24 := Equivalent.refl _

def a25 : Circuit 8 :=
  [Tdg 1, Sdg 2, CX 0 4, CX 3 6, CX 3 5, T 1, CX 7 0, T 0, H 1, Tdg 7, CX 3 6,
    CX 4 3, CX 6 1, Tdg 5, Sdg 7, Y 6, T 6, S 3, T 4, H 2, CX 4 6, CX 1 5, H 2,
    CX 4 2, H 7, CX 2 7, CX 1 6, T 3, T 3, T 7, H 3, CX 1 7, Sdg 0, CX 6 3, H 2,
    Tdg 2, Tdg 1, X 6, CX 3 5, S 6, H 2, CX 2 7, T 4, CX 4 1, S 0, CX 1 4, H 7,
    CX 0 7, Z 5, CX 2 5, Z 1, Z 3, S 6, CX 3 6, X 2, Sdg 4, S 1, Sdg 6, Tdg 3,
    CX 2 5, Tdg 3, Z 4, Sdg 6, H 7, CX 2 1, T 7, S 7, CX 5 1, CX 0 6, H 7,
    CX 2 4, T 6, T 3, CX 1 2, X 7, CX 2 1, Z 4, T 1, Y 6, CX 6 7, T 4, H 5, T 0,
    T 7, CX 4 7, S 2, Tdg 4, CX 5 3, H 0, T 1, CX 0 7, X 5, X 0, Tdg 1, T 1,
    Z 7, H 0, X 5]
def b25 : Circuit 8 :=
  [Sdg 2, CX 0 4, CX 3 5, CX 7 0, H 1, Tdg 7, CX 4 3, CX 6 1, Tdg 5, Sdg 7,
    Y 6, T 6, CX 4 6, CX 1 5, CX 4 2, H 7, CX 2 7, CX 1 6, Z 3, T 7, H 3,
    CX 1 7, CX 6 3, H 2, Tdg 2, Tdg 1, X 6, CX 3 5, H 2, CX 2 7, S 4, CX 4 1,
    CX 1 4, H 7, CX 0 7, Z 5, CX 2 5, Z 3, Z 6, CX 3 6, X 2, Sdg 1, CX 2 5, S 4,
    Z 6, H 7, CX 2 1, T 7, S 7, CX 5 1, CX 0 6, H 7, CX 2 4, T 6, Tdg 3, CX 1 2,
    X 7, CX 2 1, Z 4, Y 6, CX 6 7, H 5, S 0, T 7, CX 4 7, S 2, CX 5 3, H 0,
    CX 0 7, X 0, S 1, Z 7, H 0]
theorem s25 : a25 ≡ᵤ b25 := by
  circuit_windows
    [([H 2, H 2],
        []),
      ([T 4, T 4],
        [S 4]),
      ([Tdg 1, CX 3 6, T 1, T 0, H 1, Tdg 7, CX 3 6, CX 6 1, Tdg 5, Sdg 7, Y 6,
        T 6, CX 1 5, CX 4 2, H 7, CX 2 7, CX 1 6, T 7, CX 1 7, Sdg 0, Tdg 1,
        T 0],
        [H 1, Tdg 7, CX 6 1, Tdg 5, Sdg 7, Y 6, T 6, CX 1 5, CX 4 2, H 7,
        CX 2 7, CX 1 6, T 7, CX 1 7, Tdg 1]),
      ([S 3, T 3, T 3],
        [Z 3]),
      ([Tdg 3, T 3],
        []),
      ([S 6, S 6],
        [Z 6]),
      ([Z 1, S 1],
        [Sdg 1]),
      ([Sdg 4, Z 4],
        [S 4]),
      ([Sdg 6, Sdg 6],
        [Z 6]),
      ([T 4, Tdg 4],
        []),
      ([T 1, T 1, Tdg 1, T 1],
        [S 1]),
      ([X 5, X 5],
        [])]

def a26 : Circuit 8 :=
  [H 2, X 2, Tdg 6, H 6]
def b26 : Circuit 8 :=
  [H 2, X 2, Tdg 6, H 6]
theorem s26 : a26 ≡ᵤ b26 := Equivalent.refl _

def a27 : Circuit 8 :=
  [Z 5, Z 5, CX 1 6]
def b27 : Circuit 8 :=
  [CX 1 6]
theorem s27 : a27 ≡ᵤ b27 := by
  circuit_windows
    [([Z 5, Z 5],
        [])]

def a28 : Circuit 8 :=
  [Tdg 4, S 6, T 1, CX 2 7, H 2, CX 4 1, CX 4 5, T 4]
def b28 : Circuit 8 :=
  [S 6, T 1, CX 2 7, H 2, CX 4 1, CX 4 5]
theorem s28 : a28 ≡ᵤ b28 := by
  circuit_windows
    [([Tdg 4, T 4],
        [])]

def a29 : Circuit 8 :=
  [Sdg 3, Z 1, T 5, X 2, CX 5 6]
def b29 : Circuit 8 :=
  [Sdg 3, Z 1, T 5, X 2, CX 5 6]
theorem s29 : a29 ≡ᵤ b29 := Equivalent.refl _

def a30 : Circuit 8 :=
  [S 0, Y 6, S 0]
def b30 : Circuit 8 :=
  [Y 6, Z 0]
theorem s30 : a30 ≡ᵤ b30 := by
  circuit_windows
    [([S 0, S 0],
        [Z 0])]

def a31 : Circuit 8 :=
  [S 6, CX 3 1, CX 2 4, T 4, T 0, H 7, H 5, CX 0 7, Y 0]
def b31 : Circuit 8 :=
  [S 6, CX 3 1, CX 2 4, T 4, T 0, H 7, H 5, CX 0 7, Y 0]
theorem s31 : a31 ≡ᵤ b31 := Equivalent.refl _

def a32 : Circuit 8 :=
  [CX 0 7, CX 1 4, Sdg 0, X 3, CX 4 1, T 5, H 1, CX 2 1, S 4, Y 6, Tdg 5,
    CX 0 7, Tdg 6, Z 5, H 6, CX 7 6, Z 7, Tdg 7, Tdg 2, Z 4, T 6, Tdg 4, CX 0 4,
    S 7, T 5, CX 7 1, S 5, S 2, H 6, CX 1 2, Z 0, CX 0 2, H 5, H 0, CX 1 2]
def b32 : Circuit 8 :=
  [CX 1 4, X 3, CX 4 1, H 1, CX 2 1, Y 6, Tdg 6, H 6, CX 7 6, Tdg 7, Sdg 4,
    T 6, Tdg 4, CX 0 4, Sdg 7, CX 7 1, Tdg 5, T 2, H 6, S 0, CX 0 2, H 5, H 0]
theorem s32 : a32 ≡ᵤ b32 := by
  circuit_windows
    [([CX 0 7, Sdg 0, CX 0 7, Z 0],
        [S 0]),
      ([Tdg 2, S 2],
        [T 2]),
      ([Z 7, S 7],
        [Sdg 7]),
      ([T 5, Z 5, T 5, S 5],
        []),
      ([S 4, Z 4],
        [Sdg 4]),
      ([CX 1 2, CX 1 2],
        [])]

def a33 : Circuit 8 :=
  [CX 1 7]
def b33 : Circuit 8 :=
  [CX 1 7]
theorem s33 : a33 ≡ᵤ b33 := Equivalent.refl _

def a34 : Circuit 8 :=
  [Sdg 4, Y 5, CX 2 6, Sdg 5, H 6, H 7, Sdg 1, X 6, X 0, Tdg 3, CX 6 3,
    CX 2 5, Y 5, CX 4 3, T 2, CX 5 3, T 7, H 1, Tdg 4, Sdg 4, H 4, S 7, CX 3 6,
    Tdg 4, H 3, CX 2 1, CX 0 7, CX 0 3, S 0, CX 0 7, T 5, Sdg 0, T 7, CX 4 7,
    T 4]
def b34 : Circuit 8 :=
  [Y 5, CX 2 6, Sdg 5, H 6, H 7, Sdg 1, X 6, X 0, Tdg 3, CX 6 3, CX 2 5, Y 5,
    CX 4 3, T 2, CX 5 3, H 1, Tdg 4, Z 4, H 4, CX 3 6, H 3, CX 2 1, CX 0 3, T 5,
    Z 7, CX 4 7]
theorem s34 : a34 ≡ᵤ b34 := by
  circuit_windows
    [([Sdg 4, Sdg 4],
        [Z 4]),
      ([S 0, Sdg 0],
        []),
      ([T 7, S 7, CX 0 7, CX 0 7, T 7],
        [Z 7]),
      ([Tdg 4, T 4],
        [])]

def a35 : Circuit 8 :=
  [X 2, CX 0 1, Y 7, CX 5 3, CX 2 4, Tdg 2, CX 2 7, X 1, CX 5 7, CX 7 1,
    CX 4 2, CX 1 3, CX 3 5, CX 0 1, CX 1 0, Y 3, X 4, T 3, S 4]
def b35 : Circuit 8 :=
  [X 2, CX 0 1, Y 7, CX 5 3, CX 2 4, Tdg 2, CX 2 7, X 1, CX 5 7, CX 7 1,
    CX 4 2, CX 1 3, CX 3 5, CX 0 1, CX 1 0, Y 3, X 4, T 3, S 4]
theorem s35 : a35 ≡ᵤ b35 := Equivalent.refl _

def a36 : Circuit 8 :=
  [Sdg 5, H 7, Sdg 6, Z 6, CX 3 6, Z 5, X 1, CX 6 2, T 5, S 5, H 5, H 6, Y 0,
    H 4, CX 2 6, T 2, CX 2 1, CX 4 1, H 5, CX 7 2, CX 2 4, H 7, X 2, S 1, S 7,
    T 0, S 3, Tdg 5, T 5, Z 5, H 1, CX 6 0, Y 3, CX 4 2, T 3, H 0, CX 4 5, T 3,
    CX 2 1, H 4, CX 3 0, H 6, Z 7, Tdg 7, CX 5 1, H 1, CX 3 6, CX 3 0, CX 5 1,
    CX 5 0, Tdg 3, CX 3 4, H 0, CX 7 4, CX 0 6, H 5, CX 1 4, H 4, Tdg 1, T 6,
    Z 4, CX 5 0, Y 5, CX 4 6, Sdg 4, Y 6, Y 4, CX 4 0, CX 6 4, CX 5 6, Tdg 7]
def b36 : Circuit 8 :=
  [H 7, S 6, CX 3 6, X 1, CX 6 2, T 5, H 6, Y 0, H 4, CX 2 6, T 2, CX 2 1,
    CX 4 1, CX 7 2, CX 2 4, H 7, X 2, S 1, T 0, S 3, H 1, CX 6 0, Y 3, CX 4 2,
    H 0, CX 4 5, CX 2 1, H 4, H 6, CX 5 1, H 1, CX 3 6, CX 5 1, CX 5 0, T 3,
    CX 3 4, H 0, CX 7 4, CX 0 6, H 5, CX 1 4, H 4, Tdg 1, T 6, CX 5 0, Y 5,
    CX 4 6, S 4, Y 6, Y 4, CX 4 0, CX 6 4, CX 5 6, Z 7]
theorem s36 : a36 ≡ᵤ b36 := by
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

def a37 : Circuit 8 :=
  [T 4, Tdg 5, CX 1 3, H 3, H 7, CX 7 5, CX 3 0, S 0]
def b37 : Circuit 8 :=
  [T 4, Tdg 5, CX 1 3, H 3, H 7, CX 7 5, CX 3 0, S 0]
theorem s37 : a37 ≡ᵤ b37 := Equivalent.refl _

def a38 : Circuit 8 :=
  [T 7, T 5, X 2, T 7, H 6, T 7, CX 5 0, Z 5, Z 7, CX 4 6, CX 5 1, CX 7 6,
    CX 5 4, H 2, T 7]
def b38 : Circuit 8 :=
  [T 5, X 2, H 6, CX 5 0, Z 5, CX 4 6, CX 5 1, CX 7 6, CX 5 4, H 2]
theorem s38 : a38 ≡ᵤ b38 := by
  circuit_windows
    [([T 7, T 7, T 7, Z 7, T 7],
        [])]

def a39 : Circuit 8 :=
  [CX 3 4, CX 2 4, CX 6 3]
def b39 : Circuit 8 :=
  [CX 3 4, CX 2 4, CX 6 3]
theorem s39 : a39 ≡ᵤ b39 := Equivalent.refl _

def a40 : Circuit 8 :=
  [CX 4 1, Y 5, CX 4 1]
def b40 : Circuit 8 :=
  [Y 5]
theorem s40 : a40 ≡ᵤ b40 := by
  circuit_windows
    [([CX 4 1, CX 4 1],
        [])]

def a41 : Circuit 8 :=
  [T 6]
def b41 : Circuit 8 :=
  [T 6]
theorem s41 : a41 ≡ᵤ b41 := Equivalent.refl _

def a42 : Circuit 8 :=
  [T 4, CX 4 7, Z 3, CX 2 5, CX 5 0, H 2, Tdg 7, T 7, H 3, CX 1 0, T 2, T 2,
    T 0, Tdg 7, T 4, X 2, Z 4]
def b42 : Circuit 8 :=
  [CX 4 7, Z 3, CX 2 5, CX 5 0, H 2, H 3, CX 1 0, S 2, T 0, Tdg 7, X 2, Sdg 4]
theorem s42 : a42 ≡ᵤ b42 := by
  circuit_windows
    [([T 4, T 7, Tdg 7, T 4, Z 4],
        [Sdg 4]),
      ([T 2, T 2],
        [S 2])]

def a43 : Circuit 8 :=
  [CX 0 4, CX 1 4, CX 5 3]
def b43 : Circuit 8 :=
  [CX 0 4, CX 1 4, CX 5 3]
theorem s43 : a43 ≡ᵤ b43 := Equivalent.refl _

def a44 : Circuit 8 :=
  [H 1, H 7, CX 6 3, H 1]
def b44 : Circuit 8 :=
  [H 7, CX 6 3]
theorem s44 : a44 ≡ᵤ b44 := by
  circuit_windows
    [([H 1, H 1],
        [])]

def a45 : Circuit 8 :=
  [CX 6 4, S 7, T 5, CX 2 4, CX 3 7]
def b45 : Circuit 8 :=
  [CX 6 4, S 7, T 5, CX 2 4, CX 3 7]
theorem s45 : a45 ≡ᵤ b45 := Equivalent.refl _

def a46 : Circuit 8 :=
  [Tdg 2, CX 1 3, CX 2 7, T 4, H 6, T 7, H 4, Tdg 6, H 4, CX 7 1, T 7, CX 1 4,
    H 7, Y 5, S 5, T 7, H 6, Z 3, CX 3 6, Tdg 3, CX 5 4, S 5, H 0, H 5, Tdg 6,
    CX 4 1, H 6, Tdg 2, CX 5 4, Sdg 3, CX 5 3, CX 4 0, H 5, CX 6 1, CX 2 6, H 6,
    H 4, X 3, CX 2 4, CX 2 0, T 2, H 5]
def b46 : Circuit 8 :=
  [CX 1 3, CX 2 7, T 4, H 6, Tdg 6, CX 7 1, S 7, CX 1 4, H 7, Y 5, T 7, H 6,
    CX 3 6, CX 5 4, Z 5, H 0, H 5, Tdg 6, CX 4 1, H 6, CX 5 4, T 3, CX 5 3,
    CX 4 0, CX 6 1, CX 2 6, H 6, H 4, X 3, CX 2 4, CX 2 0, Tdg 2]
theorem s46 : a46 ≡ᵤ b46 := by
  circuit_windows
    [([Z 3, Tdg 3, Tdg 2, Sdg 3, T 2],
        [T 3]),
      ([T 7, T 7],
        [S 7]),
      ([H 4, H 4],
        []),
      ([S 5, S 5],
        [Z 5]),
      ([H 5, H 5],
        [])]

def a47 : Circuit 8 :=
  [Tdg 5, Tdg 0]
def b47 : Circuit 8 :=
  [Tdg 5, Tdg 0]
theorem s47 : a47 ≡ᵤ b47 := Equivalent.refl _

def a48 : Circuit 8 :=
  [H 2, CX 7 4, T 1, CX 7 4, Y 3, H 2, CX 5 0, H 0, T 3, S 3, S 0, S 4,
    CX 3 0, Sdg 1]
def b48 : Circuit 8 :=
  [Y 3, CX 5 0, H 0, T 3, S 3, S 0, S 4, CX 3 0, Tdg 1]
theorem s48 : a48 ≡ᵤ b48 := by
  circuit_windows
    [([H 2, T 1, H 2, Sdg 1],
        [Tdg 1]),
      ([CX 7 4, CX 7 4],
        [])]

def a49 : Circuit 8 :=
  [Z 5, CX 7 5, CX 6 2]
def b49 : Circuit 8 :=
  [Z 5, CX 7 5, CX 6 2]
theorem s49 : a49 ≡ᵤ b49 := Equivalent.refl _

def a50 : Circuit 8 :=
  [Tdg 6, H 5, Y 3, CX 2 1, CX 3 5, H 7, T 0, CX 0 7, H 4, H 3, S 5, X 5,
    Tdg 0, T 2, S 5, Tdg 5, CX 3 5, Tdg 6]
def b50 : Circuit 8 :=
  [H 5, Y 3, CX 2 1, CX 3 5, H 7, CX 0 7, H 4, H 3, S 5, X 5, T 2, T 5,
    CX 3 5, Sdg 6]
theorem s50 : a50 ≡ᵤ b50 := by
  circuit_windows
    [([T 0, Tdg 0],
        []),
      ([Tdg 6, Tdg 6],
        [Sdg 6]),
      ([S 5, Tdg 5],
        [T 5])]

def a51 : Circuit 8 :=
  [Y 0, H 2, CX 7 5, CX 1 6]
def b51 : Circuit 8 :=
  [Y 0, H 2, CX 7 5, CX 1 6]
theorem s51 : a51 ≡ᵤ b51 := Equivalent.refl _

def a52 : Circuit 8 :=
  [Sdg 6, CX 1 7]
def b52 : Circuit 8 :=
  [CX 1 7, Sdg 6]
theorem s52 : a52 ≡ᵤ b52 := by
  circuit_windows
    []

def a53 : Circuit 8 :=
  [T 6, Tdg 6, CX 6 3]
def b53 : Circuit 8 :=
  [CX 6 3]
theorem s53 : a53 ≡ᵤ b53 := by
  circuit_windows
    [([T 6, Tdg 6],
        [])]

def a54 : Circuit 8 :=
  [Z 5, H 1, CX 5 0, CX 1 7, CX 1 0]
def b54 : Circuit 8 :=
  [Z 5, H 1, CX 5 0, CX 1 7, CX 1 0]
theorem s54 : a54 ≡ᵤ b54 := Equivalent.refl _

theorem equiv : original ≡ᵤ optimized :=
  calc original = a0 ++ (a1 ++ (a2 ++ (a3 ++ (a4 ++ (a5 ++ (a6 ++ (a7 ++ (a8 ++ (a9 ++ (a10 ++ (a11 ++ (a12 ++ (a13 ++ (a14 ++ (a15 ++ (a16 ++ (a17 ++ (a18 ++ (a19 ++ (a20 ++ (a21 ++ (a22 ++ (a23 ++ (a24 ++ (a25 ++ (a26 ++ (a27 ++ (a28 ++ (a29 ++ (a30 ++ (a31 ++ (a32 ++ (a33 ++ (a34 ++ (a35 ++ (a36 ++ (a37 ++ (a38 ++ (a39 ++ (a40 ++ (a41 ++ (a42 ++ (a43 ++ (a44 ++ (a45 ++ (a46 ++ (a47 ++ (a48 ++ (a49 ++ (a50 ++ (a51 ++ (a52 ++ (a53 ++ (a54)))))))))))))))))))))))))))))))))))))))))))))))))))))) := rfl
    _ ≡ᵤ b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ (b7 ++ (b8 ++ (b9 ++ (b10 ++ (b11 ++ (b12 ++ (b13 ++ (b14 ++ (b15 ++ (b16 ++ (b17 ++ (b18 ++ (b19 ++ (b20 ++ (b21 ++ (b22 ++ (b23 ++ (b24 ++ (b25 ++ (b26 ++ (b27 ++ (b28 ++ (b29 ++ (b30 ++ (b31 ++ (b32 ++ (b33 ++ (b34 ++ (b35 ++ (b36 ++ (b37 ++ (b38 ++ (b39 ++ (b40 ++ (b41 ++ (b42 ++ (b43 ++ (b44 ++ (b45 ++ (b46 ++ (b47 ++ (b48 ++ (b49 ++ (b50 ++ (b51 ++ (b52 ++ (b53 ++ (b54)))))))))))))))))))))))))))))))))))))))))))))))))))))) := s0.append (s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append (s8.append (s9.append (s10.append (s11.append (s12.append (s13.append (s14.append (s15.append (s16.append (s17.append (s18.append (s19.append (s20.append (s21.append (s22.append (s23.append (s24.append (s25.append (s26.append (s27.append (s28.append (s29.append (s30.append (s31.append (s32.append (s33.append (s34.append (s35.append (s36.append (s37.append (s38.append (s39.append (s40.append (s41.append (s42.append (s43.append (s44.append (s45.append (s46.append (s47.append (s48.append (s49.append (s50.append (s51.append (s52.append (s53.append (s54))))))))))))))))))))))))))))))))))))))))))))))))))))))
    _ = optimized := rfl

end Quantum.Circuit.Harness
