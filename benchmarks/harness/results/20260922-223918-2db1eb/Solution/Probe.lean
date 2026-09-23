import Solution.Data
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
namespace Quantum.Circuit.Harness
open Instr
#eval (phasePolyChecker 48).check d0 (e0 ++ residual)
#eval (phasePolyChecker 48).check (residual ++ d1) e1
end Quantum.Circuit.Harness
