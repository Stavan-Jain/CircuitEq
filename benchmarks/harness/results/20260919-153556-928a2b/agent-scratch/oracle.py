import re, sys
sys.path.insert(0, "scripts")
import numpy as np
import tcount_survey as ts
src = open("Harness/Task.lean").read()
def grab(name):
    m = re.search(r"def %s : Circuit 8 :=\s*\[(.*?)\]" % name, src, re.S)
    return [g.strip() for g in re.sub(r"\s+", " ", m.group(1)).split(",")]
a = ts.parse(grab("original")); b = ts.parse(grab("optimized"))
print(len(a), len(b))
Ua = ts.unitary(a, 8); Ub = ts.unitary(b, 8)
print(ts.compare(Ua, Ub))
D = Ua - Ub
bad = [k for k in range(256) if np.linalg.norm(D[:, k]) > 1e-6]
print("differing columns:", bad[:10], len(bad))
