import sys, pickle
sys.path.insert(0, "scripts")
import tcount_survey as ts, numpy as np
xs, ys, cuts = pickle.load(open(sys.argv[1],"rb"))
a=xs[440:544]; b=ys[331:399]
print("A:", " ".join(ts.show(g) for g in a)); print("B:", " ".join(ts.show(g) for g in b))
rng=np.random.default_rng(3)
psi=rng.normal(size=256)+1j*rng.normal(size=256); psi/=np.linalg.norm(psi); psi=psi.reshape([2]*8)
def pref(gs):
    st=[psi]; s=psi
    for g in gs: s=ts._apply(s,g); st.append(s)
    return st
pa=pref(a); pb=pref(b)
# phase-insensitive matches
for i,s in enumerate(pa):
    for j,t in enumerate(pb):
        ov=abs(np.vdot(s.ravel(),t.ravel()))
        if ov>1-1e-8: print("match", i, j, "phase-only" if np.linalg.norm(s-t)>1e-6 else "exact")
