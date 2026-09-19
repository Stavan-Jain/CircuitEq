import re, sys, time
sys.path.insert(0, "scripts")
import numpy as np
import tcount_survey as ts
src = open("Harness/Task.lean").read()
def grab(name):
    m = re.search(r"def %s : Circuit 8 :=\s*\[(.*?)\]" % name, src, re.S)
    return [g.strip() for g in re.sub(r"\s+", " ", m.group(1)).split(",")]
a = ts.parse(grab("original")); b = ts.parse(grab("optimized"))
rng = np.random.default_rng(1)
psi0 = rng.normal(size=256) + 1j*rng.normal(size=256); psi0 /= np.linalg.norm(psi0); psi0 = psi0.reshape([2]*8)
def prefixes(gs):
    out=[psi0]; s=psi0
    for g in gs:
        s = ts._apply(s, g); out.append(s)
    return out
pa = prefixes(a); pb = prefixes(b)
def key(v): return tuple(np.round(v.reshape(-1), 6).view(float))
hb = {}
for j, v in enumerate(pb): hb.setdefault(key(v), []).append(j)
cuts = [(0,0)]
for i in range(1, len(a)+1):
    js = hb.get(key(pa[i]), [])
    js = [j for j in js if j > cuts[-1][1]]
    if js and i - cuts[-1][0] >= 1:
        cuts.append((i, js[0]))
if cuts[-1] != (len(a), len(b)): cuts.append((len(a), len(b)))
print(len(cuts), "cuts")
segs = [(a[i0:i1], b[j0:j1]) for (i0,j0),(i1,j1) in zip(cuts, cuts[1:])]
# merge to segments of at least ~min size? keep small. print stats
sizes = [(len(x), len(y)) for x,y in segs]
print(max(sizes), sizes[:40])
import pickle
pickle.dump((a,b,cuts), open(sys.argv[1], "wb"))
