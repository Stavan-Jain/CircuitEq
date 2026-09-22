import CircuitEq
import Harness.Task
import Solution.Seg0
import Solution.Seg1
import Solution.Seg2
import Solution.Seg3
import Solution.Seg4
import Solution.Seg5
import Solution.Seg6
import Solution.Seg7
import Solution.Seg8
import Solution.Seg9
import Solution.Seg10
import Solution.Seg11
import Solution.Seg12
import Solution.Seg13
import Solution.Seg14
import Solution.Seg15
import Solution.Seg16
import Solution.Seg17
import Solution.Seg18

/-! # Solution

The pair is cut into segments at points where the two circuits agree on the
state; each segment is proved by `circuit_windows` in its own module under
`Solution/`, and the segments are assembled here by `Equivalent.append`.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The claim holds. -/
theorem equiv : original ≡ᵤ optimized :=
  calc original = Seg.a0 ++ (Seg.a1 ++ (Seg.a2 ++ (Seg.a3 ++ (Seg.a4 ++ (Seg.a5 ++ (Seg.a6 ++ (Seg.a7 ++ (Seg.a8 ++ (Seg.a9 ++ (Seg.a10 ++ (Seg.a11 ++ (Seg.a12 ++ (Seg.a13 ++ (Seg.a14 ++ (Seg.a15 ++ (Seg.a16 ++ (Seg.a17 ++ (Seg.a18)))))))))))))))))) := by decide +kernel
    _ ≡ᵤ Seg.b0 ++ (Seg.b1 ++ (Seg.b2 ++ (Seg.b3 ++ (Seg.b4 ++ (Seg.b5 ++ (Seg.b6 ++ (Seg.b7 ++ (Seg.b8 ++ (Seg.b9 ++ (Seg.b10 ++ (Seg.b11 ++ (Seg.b12 ++ (Seg.b13 ++ (Seg.b14 ++ (Seg.b15 ++ (Seg.b16 ++ (Seg.b17 ++ (Seg.b18)))))))))))))))))) := Seg.s0.append (Seg.s1.append (Seg.s2.append (Seg.s3.append (Seg.s4.append (Seg.s5.append (Seg.s6.append (Seg.s7.append (Seg.s8.append (Seg.s9.append (Seg.s10.append (Seg.s11.append (Seg.s12.append (Seg.s13.append (Seg.s14.append (Seg.s15.append (Seg.s16.append (Seg.s17.append (Seg.s18))))))))))))))))))
    _ = optimized := by decide +kernel

/-- The claim fails. -/
theorem not_equiv : ¬ (original ≡ᵤ optimized) := by
  sorry

end Quantum.Circuit.Harness
