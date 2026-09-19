import sys, pickle
sys.path.insert(0, "scripts")
import tcount_survey as ts, numpy as np
xs, ys, cuts = pickle.load(open(sys.argv[1],"rb"))
a=xs[440:544]; b=ys[331:399]
for w in range(8):
    print(w, "A:", [(i,ts.show(g)) for i,g in enumerate(a) if w in g[1]])
    print(w, "B:", [(j,ts.show(g)) for j,g in enumerate(b) if w in g[1]])
print(a[0])
