import sys, pickle, time
sys.path.insert(0, "scripts")
import tcount_survey as ts
a, b, cuts = pickle.load(open(sys.argv[1], "rb"))
segs = [(a[i0:i1], b[j0:j1]) for (i0,j0),(i1,j1) in zip(cuts, cuts[1:])]
# merge consecutive identical segments
merged = []
for x, y in segs:
    same = x == y
    if merged and merged[-1][2] and same:
        merged[-1][0].extend(x); merged[-1][1].extend(y)
    else:
        merged.append([list(x), list(y), same])
out = ["import CircuitEq", "import Harness.Task", "", "set_option maxHeartbeats 4000000", "set_option maxRecDepth 4000", "",
       "namespace Quantum.Circuit.Harness", "", "open Instr", ""]
names = []
for k, (x, y, same) in enumerate(merged):
    out.append(f"def a{k} : Circuit 8 :=\n  {ts.lean_list(x, 4)}")
    out.append(f"def b{k} : Circuit 8 :=\n  {ts.lean_list(y, 4)}")
    if same:
        out.append(f"theorem s{k} : a{k} ≡ᵤ b{k} := Equivalent.refl _")
    else:
        t0 = time.time(); al = None
        for canon in ts.CANONS:
            for rm in (True, False):
                al, rep = ts.search(x, y, canon, rm)
                if al is not None: break
            if al is not None: break
        print(k, len(x), len(y), "search", round(time.time()-t0,1), None if al is None else al.stats(), file=sys.stderr)
        if al is None:
            out.append(f"theorem s{k} : a{k} ≡ᵤ b{k} := by sorry -- FAILED")
        else:
            out.append(f"theorem s{k} : a{k} ≡ᵤ b{k} := by\n  circuit_windows\n    {ts.lean_windows(al)}")
    out.append("")
    names.append(k)
def nest(pref, ks):
    if len(ks) == 1: return f"{pref}{ks[0]}"
    return f"{pref}{ks[0]} ++ ({nest(pref, ks[1:])})"
def nesth(ks):
    if len(ks) == 1: return f"s{ks[0]}"
    return f"s{ks[0]}.append ({nesth(ks[1:])})"
out.append(f"theorem equiv : original ≡ᵤ optimized :=\n  calc original = {nest('a', names)} := rfl\n    _ ≡ᵤ {nest('b', names)} := {nesth(names)}\n    _ = optimized := rfl")
out.append("")
out.append("end Quantum.Circuit.Harness")
open(sys.argv[2], "w").write("\n".join(out) + "\n")
print(len(merged), "segments")
