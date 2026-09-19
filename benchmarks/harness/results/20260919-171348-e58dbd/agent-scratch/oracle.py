import sys, re
sys.path.insert(0, "scripts")
import tcount_survey as ts
import numpy as np
src = open("Harness/Task.lean").read()
def gates(name):
    m = re.search(r"def %s : Circuit 8 :=\s*\[(.*?)\]" % name, src, re.S)
    return [g.strip() for g in m.group(1).replace("\n"," ").split(",")]
o = gates("original"); p = gates("optimized")
print(len(o), len(p))
xs = ts.parse(o); ys = ts.parse(p)
U = ts.unitary(xs, 8); V = ts.unitary(ys, 8)
print(ts.compare(U, V))
# per basis vector diff
d = [np.linalg.norm(U[:,k]-V[:,k]) for k in range(256)]
bad = [k for k in range(256) if d[k] > 1e-9]
print("differing basis vectors:", len(bad), bad[:10])
# phase check
r = np.trace(U.conj().T @ V)/256
print("overlap", r, abs(r))
