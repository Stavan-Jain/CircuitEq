import Solution.Normalize
import Solution.Gather
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
namespace Quantum.Circuit.Harness
open Instr

theorem diagonal0 : d0 ≡ᵤ e0 ++ residual :=
  (phasePolyChecker 48).sound _ _ (by decide +kernel)

theorem diagonal1 : residual ++ d1 ≡ᵤ e1 :=
  (phasePolyChecker 48).sound _ _ (by decide +kernel)

theorem residual_comm : residual ++ middle ≡ᵤ middle ++ residual :=
  checked_comm _ _ (by decide +kernel)

theorem original_normal : original ≡ᵤ h0 ++ d0 ++ middle ++ d1 ++ h1 := by
  exact (((Equivalent.refl h0).append normalize0).append
    (Equivalent.refl middle)).append (normalize1.append (Equivalent.refl h1))

theorem between_normal : h0 ++ d0 ++ middle ++ d1 ++ h1 ≡ᵤ
    h0 ++ e0 ++ middle ++ e1 ++ h1 := by
  calc
    _ ≡ᵤ h0 ++ (e0 ++ residual) ++ middle ++ d1 ++ h1 :=
      (((Equivalent.refl h0).append diagonal0).append (Equivalent.refl middle)).append
        ((Equivalent.refl d1).append (Equivalent.refl h1))
    _ ≡ᵤ h0 ++ e0 ++ middle ++ (residual ++ d1) ++ h1 := by
      simpa only [List.append_assoc] using residual_comm.in_context (h0 ++ e0) (d1 ++ h1)
    _ ≡ᵤ _ := by
      simpa only [List.append_assoc] using diagonal1.in_context (h0 ++ e0 ++ middle) h1
end Quantum.Circuit.Harness
