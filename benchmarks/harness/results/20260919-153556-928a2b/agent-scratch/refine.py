import sys, pickle, time
sys.path.insert(0, "scripts")
import tcount_survey as ts
a, b, cuts = pickle.load(open(sys.argv[1], "rb"))
segs = [(a[i0:i1], b[j0:j1]) for (i0,j0),(i1,j1) in zip(cuts, cuts[1:])]
merged = []
for x, y in segs:
    same = x == y
    if merged and merged[-1][2] and same:
        merged[-1][0].extend(x); merged[-1][1].extend(y)
    else:
        merged.append([list(x), list(y), same])
for k in (18, 23, 25):
    x, y, _ = merged[k]
    t0 = time.time()
    al, att, which = ts.best_alignment(x, y)
    print(k, round(time.time()-t0,1), which, None if al is None else al.stats())
    if al is not None:
        print(f"theorem s{k} : a{k} ≡ᵤ b{k} := by\n  circuit_windows\n    {ts.lean_windows(al)}")
