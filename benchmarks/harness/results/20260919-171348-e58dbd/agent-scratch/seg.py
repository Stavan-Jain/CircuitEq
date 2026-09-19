import sys, re, pickle
sys.path.insert(0, "scripts")
import tcount_survey as ts
import numpy as np
src = open("Harness/Task.lean").read()
def gates(name):
    m = re.search(r"def %s : Circuit 8 :=\s*\[(.*?)\]" % name, src, re.S)
    return [g.strip() for g in m.group(1).replace("\n"," ").split(",")]
o = gates("original"); p = gates("optimized")
xs = ts.parse(o); ys = ts.parse(p)
rng = np.random.default_rng(1)
psi = rng.normal(size=256)+1j*rng.normal(size=256); psi/=np.linalg.norm(psi); psi=psi.reshape([2]*8)
def prefixes(gs):
    st=[psi.copy()]; s=psi.copy()
    for g in gs:
        s = ts._apply(s, g); st.append(s)
    return st
po = prefixes(xs); pp = prefixes(ys)
def key(s): return tuple(np.round(s.ravel(),7).view(float).tolist())
dp = {}
for j,s in enumerate(pp): dp.setdefault(key(s), []).append(j)
matches = []
for i,s in enumerate(po):
    k = key(s)
    if k in dp: matches.append((i, dp[k]))
print("match count", len(matches))
# choose cuts: greedy, segment of original <= 60 gates, j monotone
cuts=[(0,0)]; 
target=60
while True:
    i0,j0 = cuts[-1]
    cand=[(i,js) for i,js in matches if i0<i<=i0+target and any(j>j0 for j in js)]
    if not cand: 
        cand=[(i,js) for i,js in matches if i>i0 and any(j>j0 for j in js)]
        if not cand: break
        i,js=cand[0]
    else:
        i,js=cand[-1]
    j=min(j for j in js if j>j0)
    cuts.append((i,j))
    if i==len(xs): break
print(cuts)
print(cuts[-1], len(xs), len(ys))
pickle.dump((xs,ys,cuts), open(sys.argv[1],"wb"))
