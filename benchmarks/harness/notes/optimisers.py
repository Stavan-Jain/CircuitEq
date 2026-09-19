"""Run PyZX's pipelines on the harness pair's original circuit and measure how far each
output is from the original: counts, numerical equality, and how well it segments."""
import json, sys, time
import numpy as np
sys.path.insert(0, "scripts")
import pyzx as zx
import check_pyzx_benchmarks as cpb
import tcount_survey as ts

pair = json.load(open(sys.argv[1]))
n, orig, twin = pair["qubits"], pair["original"], pair["optimized"]

def to_pyzx(gates):
    """PyZX has no Y gate in this pipeline; Y = S X Sdg exactly (time order Sdg, X, S)."""
    c = zx.Circuit(n)
    quarter = {"T": 1, "S": 2, "Z": 4, "Sdg": 6, "Tdg": 7}
    for g in gates:
        name, *w = g.split(); w = [int(x) for x in w]
        if name == "CX": c.add_gate("CNOT", w[0], w[1])
        elif name == "H": c.add_gate("HAD", w[0])
        elif name == "X": c.add_gate("NOT", w[0])
        elif name == "Y":
            c.add_gate("ZPhase", w[0], phase=zx.utils.Fraction(6, 4)); c.add_gate("NOT", w[0]); c.add_gate("ZPhase", w[0], phase=zx.utils.Fraction(2, 4))
        else: c.add_gate("ZPhase", w[0], phase=zx.utils.Fraction(quarter[name], 4))
    return c

def tcount(gates): return sum(g.split()[0] in ("T", "Tdg") for g in gates)

def prefix_states(gates, psi):
    """All prefix states of a gate list on one input state: (len+1) x 2^n."""
    out = [psi]
    for g in ts.parse(gates):
        psi = ts._apply(psi, g) if hasattr(ts, "_apply") else None
        out.append(psi)
    return np.array([s.reshape(-1) for s in out])

def segmentation(a, b):
    """Cut points: pairs (i, j) where the prefixes agree up to a global phase on a random
    state. Returns the number of cuts on the longest increasing chain and the longest gap."""
    rng = np.random.default_rng(1)
    psi = rng.normal(size=2 ** n) + 1j * rng.normal(size=2 ** n); psi /= np.linalg.norm(psi)
    psi = psi.reshape([2] * n)
    A, B = prefix_states(a, psi), prefix_states(b, psi)
    ov = np.abs(A.conj() @ B.T)                      # |<a_i|b_j>|
    exact = np.abs((A.conj() @ B.T) - 1) < 1e-9      # equal including the phase
    def chain(mask):
        cuts, j0 = [(0, 0)], 0
        for i in range(1, len(A)):
            js = np.nonzero(mask[i, j0 + 1:])[0]
            if len(js): j0 = j0 + 1 + js[0]; cuts.append((i, j0))
        if cuts[-1] != (len(A) - 1, len(B) - 1): cuts.append((len(A) - 1, len(B) - 1))
        gaps = [(c2[0] - c1[0]) + (c2[1] - c1[1]) for c1, c2 in zip(cuts, cuts[1:])]
        return len(cuts) - 1, max(gaps)
    return chain(ov > 1 - 1e-9), chain(exact)

rows = [("peephole (mine)", twin)]
c0 = to_pyzx(orig)
for name in ("teleport", "full_reduce"):
    t0 = time.time(); out = cpb.optimize(c0, name); dt = time.time() - t0
    rows.append((f"pyzx {name}", cpb.lean_instructions(out)))
    print(f"ran pyzx {name} in {dt:.1f} s", flush=True)
t0 = time.time(); basic = zx.optimize.basic_optimization(c0.to_basic_gates()); 
rows.append(("pyzx basic_optimization", cpb.lean_instructions(basic)))

U = ts.unitary(ts.parse(orig), n)
print(f"\noriginal: {len(orig)} gates, T-count {tcount(orig)}, {sum(g.startswith('H') for g in orig)} H, {sum(g.startswith('CX') for g in orig)} CX\n")
print(f"{'twin':26} {'gates':>6} {'T':>4} {'CX':>5}  {'equal?':16} {'segments (up to phase)':>24} {'longest':>8} {'segments (exact)':>18} {'longest':>8}")
for name, gates in rows:
    verdict = ts.compare(U, ts.unitary(ts.parse(gates), n))
    (k, gap), (k2, gap2) = segmentation(orig, gates)
    print(f"{name:26} {len(gates):>6} {tcount(gates):>4} {sum(g.startswith('CX') for g in gates):>5}  {str(verdict[0]):16} {k:>24} {gap:>8} {k2:>18} {gap2:>8}")
    json.dump({"name": name, "gates": gates}, open(f"{sys.argv[2]}/{name.replace(' ', '_').replace('(', '').replace(')', '')}.json", "w"))
