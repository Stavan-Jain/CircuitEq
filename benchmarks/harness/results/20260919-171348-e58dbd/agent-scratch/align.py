import sys, pickle, time
sys.path.insert(0, "scripts")
import tcount_survey as ts
xs, ys, cuts = pickle.load(open(sys.argv[1],"rb"))
res=[]
for (i0,j0),(i1,j1) in zip(cuts,cuts[1:]):
    a=xs[i0:i1]; b=ys[j0:j1]
    t=time.time()
    al, att, which = ts.best_alignment(a,b)
    dt=time.time()-t
    if al is None:
        print(f"seg {i0}-{i1} / {j0}-{j1} ({len(a)},{len(b)}): FAIL {dt:.1f}s", flush=True)
        res.append(None)
    else:
        st=al.stats()
        print(f"seg {i0}-{i1} / {j0}-{j1} ({len(a)},{len(b)}): {st} {which} {dt:.1f}s", flush=True)
        res.append(ts.lean_windows(al))
pickle.dump(res, open(sys.argv[2],"wb"))
