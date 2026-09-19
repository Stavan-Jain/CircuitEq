import sys, pickle
sys.path.insert(0, "scripts")
import tcount_survey as ts
xs, ys, cuts = pickle.load(open(sys.argv[1],"rb"))
wins = pickle.load(open(sys.argv[2],"rb"))
segs = list(zip(cuts, cuts[1:]))
imports=[]; names=[]
for k,(((i0,j0),(i1,j1)),w) in enumerate(zip(segs,wins)):
    a=xs[i0:i1]; b=ys[j0:j1]
    body = f"  circuit_windows\n    {w}" if w is not None else "  sorry"
    if w is not None and w.strip()=="[]": body = "  circuit_simp"
    mod = f"""import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a{k} : Circuit 8 :=
  {ts.lean_list(a,4)}

def b{k} : Circuit 8 :=
  {ts.lean_list(b,4)}

theorem s{k} : a{k} ≡ᵤ b{k} := by
{body}

end Quantum.Circuit.Harness.Seg
"""
    open(f"Solution/Seg{k}.lean","w").write(mod)
    imports.append(f"import Solution.Seg{k}"); names.append(k)
def nest(pref, ks):
    if len(ks)==1: return f"{pref}{ks[0]}"
    return f"{pref}{ks[0]} ++ ({nest(pref, ks[1:])})"
def nesth(ks):
    if len(ks)==1: return f"Seg.s{ks[0]}"
    return f"Seg.s{ks[0]}.append ({nesth(ks[1:])})"
sol = f"""import CircuitEq
import Harness.Task
{chr(10).join(imports)}

/-! # Solution

The pair is cut into segments at points where the two circuits agree on the
state; each segment is proved by `circuit_windows` in its own module under
`Solution/`, and the segments are assembled here by `Equivalent.append`.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The claim holds. -/
theorem equiv : original ≡ᵤ optimized :=
  calc original = {nest("Seg.a", names)} := rfl
    _ ≡ᵤ {nest("Seg.b", names)} := {nesth(names)}
    _ = optimized := rfl

/-- The claim fails. -/
theorem not_equiv : ¬ (original ≡ᵤ optimized) := by
  sorry

end Quantum.Circuit.Harness
"""
open("Solution.lean","w").write(sol)
