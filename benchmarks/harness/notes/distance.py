"""How far is each twin from the original once both lists are put in one canonical order?
Two views: (1) how much of the gate list a diff matches, (2) how finely the pair cuts into
segments whose prefixes agree up to a global phase."""
import json, sys, difflib
import numpy as np
sys.path.insert(0, "scripts")
import tcount_survey as ts
S = sys.argv[1]
pair = json.load(open(f"{S}/pair.json")); n = pair["qubits"]
twins = {"peephole (mine)": pair["optimized"]}
for f in ("pyzx_teleport", "pyzx_full_reduce"):
    twins[f.replace("_", " ", 1)] = json.load(open(f"{S}/{f}.json"))["gates"]

def canon(gates, how):
    g = ts.parse(gates); order = ts.canonical_order(g, how)
    return [g[i] for i in order]

def prefixes(g, psi):
    out = [psi]
    for x in g:
        psi = ts._apply(psi, x); out.append(psi)
    return np.array([s.reshape(-1) for s in out])

rng = np.random.default_rng(1)
psi = rng.normal(size=2 ** n) + 1j * rng.normal(size=2 ** n); psi = (psi / np.linalg.norm(psi)).reshape([2] * n)

print(f"{'twin':20} {'order':18} {'diff-matched':>13} {'segments':>9} {'longest segment (gates, both sides)':>36}")
for name, gates in twins.items():
    for how in ("raw", "greedy/cancommute", "asap/cancommute"):
        a, b = canon(pair["original"], how), canon(gates, how)
        sm = difflib.SequenceMatcher(None, [ts.show(x) for x in a], [ts.show(x) for x in b], autojunk=False)
        matched = sum(m.size for m in sm.get_matching_blocks())
        A, B = prefixes(a, psi), prefixes(b, psi)
        ok = np.abs(A.conj() @ B.T) > 1 - 1e-9
        cuts, j0 = [(0, 0)], 0
        for i in range(1, len(A)):
            js = np.nonzero(ok[i, j0 + 1:])[0]
            if len(js): j0 += 1 + js[0]; cuts.append((i, j0))
        if cuts[-1] != (len(a), len(b)): cuts.append((len(a), len(b)))
        gaps = [(c2[0] - c1[0]) + (c2[1] - c1[1]) for c1, c2 in zip(cuts, cuts[1:])]
        print(f"{name:20} {how:18} {matched:>6}/{len(a):<6} {len(gaps):>9} {max(gaps):>36}")
