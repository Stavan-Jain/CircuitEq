import re, sys, pickle, time
sys.path.insert(0, "scripts")
import tcount_survey as ts
src = open("Harness/Task.lean").read()
def grab(name):
    m = re.search(r"def %s : Circuit 8 :=\s*\[(.*?)\]" % name, src, re.S)
    return [g.strip() for g in re.sub(r"\s+", " ", m.group(1)).split(",")]
a = ts.parse(grab("original")); b = ts.parse(grab("optimized"))
t0=time.time()
al, attempts, which = ts.best_alignment(a, b)
print("time", time.time()-t0, which)
if al is None:
    print(attempts)
else:
    print(al.stats())
    for d in al.describe(): print(d)
    pickle.dump(al, open("/private/tmp/claude-501/-Users-stavanjain--circuiteq-harness-runs-20260919-153556-928a2b-ws/7f9ed7ab-8998-4127-acee-4234b8d5717d/scratchpad/al.pkl","wb"))
