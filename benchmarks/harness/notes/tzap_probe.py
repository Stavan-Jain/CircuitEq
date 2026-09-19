"""Run TZAP on a circuit given as our gate strings and measure its output against the
original: counts, whether it is equal exactly or only up to a global phase, and how far it
is from the original as a gate list (diff after canonical ordering, segments between points
where the prefix states agree up to a phase).

    /tmp/circuiteq-pyzx-venv/bin/python benchmarks/harness/notes/tzap_probe.py PAIR.json OUTDIR

PAIR.json has `qubits` and `original` (the harness's pair format). TZAP is the command
`~/.circuiteq-harness/envs/tzap/bin/tzap` (pip wheel tzap==0.6.1, installed without its
optional Qiskit and PennyLane dependencies). TZAP has no `y` gate: `Y = S X Sdg` exactly,
so a `Y q` is written `sdg q; x q; s q`.
"""
import difflib, json, math, re, subprocess, sys, time
from fractions import Fraction
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
import tcount_survey as ts

TZAP = str(Path.home() / ".circuiteq-harness/envs/tzap/bin/tzap")
PHASES = {0: [], 1: ["T"], 2: ["S"], 3: ["S", "T"], 4: ["Z"], 5: ["Z", "T"], 6: ["Sdg"], 7: ["Tdg"]}
QASM = {"H": "h", "X": "x", "Z": "z", "S": "s", "Sdg": "sdg", "T": "t", "Tdg": "tdg"}


def to_qasm(gates, n):
    out = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{n}];"]
    for g in gates:
        name, *w = g.split()
        if name == "CX": out.append(f"cx q[{w[0]}],q[{w[1]}];")
        elif name == "Y": out += [f"sdg q[{w[0]}];", f"x q[{w[0]}];", f"s q[{w[0]}];"]
        else: out.append(f"{QASM[name]} q[{w[0]}];")
    return "\n".join(out) + "\n"


def angle(text):
    """An angle expression of pi as a number of eighth-turns of the phase (units of pi/4)."""
    value = eval(text.replace("pi", "math.pi"), {"math": math})
    k = value / (math.pi / 4)
    if abs(k - round(k)) > 1e-9:
        raise ValueError(f"not a multiple of pi/4: {text}")
    return int(round(k)) % 8


def from_qasm(text):
    gates, back = [], {v: k for k, v in QASM.items()}
    for line in text.splitlines():
        line = line.strip().rstrip(";")
        if not line or line.startswith(("OPENQASM", "include", "qreg", "creg", "//")): continue
        m = re.match(r"(\w+)(?:\(([^)]*)\))?\s+(.*)", line)
        name, arg, wires = m[1], m[2], [int(x) for x in re.findall(r"\[(\d+)\]", m[3])]
        if name == "cx": gates.append(f"CX {wires[0]} {wires[1]}")
        elif name == "cz": gates += [f"H {wires[1]}", f"CX {wires[0]} {wires[1]}", f"H {wires[1]}"]
        elif name == "rz": gates += [f"{p} {wires[0]}" for p in PHASES[angle(arg)]]   # diag(1, e^{i theta})
        elif name in back: gates.append(f"{back[name]} {wires[0]}")
        else: raise ValueError(f"unexpected gate in TZAP output: {line}")
    return gates


def tcount(gates): return sum(g.split()[0] in ("T", "Tdg") for g in gates)


def distance(a, b, n, how):
    ga, gb = ts.parse(a), ts.parse(b)
    ga, gb = [ga[i] for i in ts.canonical_order(ga, how)], [gb[i] for i in ts.canonical_order(gb, how)]
    sm = difflib.SequenceMatcher(None, [ts.show(x) for x in ga], [ts.show(x) for x in gb], autojunk=False)
    matched = sum(m.size for m in sm.get_matching_blocks())
    rng = np.random.default_rng(1)
    psi = rng.normal(size=2 ** n) + 1j * rng.normal(size=2 ** n)
    psi = (psi / np.linalg.norm(psi)).reshape([2] * n)
    def prefixes(g):
        out, s = [psi], psi
        for x in g:
            s = ts._apply(s, x); out.append(s)
        return np.array([v.reshape(-1) for v in out])
    A, B = prefixes(ga), prefixes(gb)
    ok = np.abs(A.conj() @ B.T) > 1 - 1e-9
    cuts, j0 = [(0, 0)], 0
    for i in range(1, len(A)):
        js = np.nonzero(ok[i, j0 + 1:])[0]
        if len(js): j0 += 1 + js[0]; cuts.append((i, j0))
    if cuts[-1] != (len(ga), len(gb)): cuts.append((len(ga), len(gb)))
    gaps = [(c2[0] - c1[0]) + (c2[1] - c1[1]) for c1, c2 in zip(cuts, cuts[1:])]
    return matched, len(gaps), max(gaps)


def main():
    pair = json.load(open(sys.argv[1])); out = Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
    n, orig = pair["qubits"], pair["original"]
    (out / "original.qasm").write_text(to_qasm(orig, n))
    U = ts.unitary(ts.parse(orig), n) if n <= 10 else None
    print(f"original: {len(orig)} gates, T-count {tcount(orig)}, {sum(g.startswith('CX') for g in orig)} CX")
    print(f"{'tzap level':12} {'time':>7} {'gates':>6} {'T':>4} {'CX':>5} {'equal?':>8} {'diff-matched':>14} {'segments':>9} {'longest':>8}   output gate names")
    for level in ("-O1", "-O2", "-O3", "-Osuper"):
        dst = out / f"tzap{level}.qasm"
        t0 = time.time()
        run = subprocess.run([TZAP, str(out / "original.qasm"), "-o", str(dst), level, "--decompose-rz", "--decompose-cz"],
                             capture_output=True, text=True, timeout=600)
        dt = time.time() - t0
        if run.returncode != 0:
            print(f"{level:12} failed: {(run.stderr or run.stdout).strip()[:200]}"); continue
        text = dst.read_text()
        names = sorted(set(re.findall(r"^(\w+)", text, re.M)) - {"OPENQASM", "include", "qreg", "creg"})
        gates = from_qasm(text)
        verdict = ts.compare(U, ts.unitary(ts.parse(gates), n))[0] if U is not None else "n/a"
        matched, segs, longest = distance(orig, gates, n, "greedy/cancommute")
        print(f"{level:12} {dt:>6.2f}s {len(gates):>6} {tcount(gates):>4} {sum(g.startswith('CX') for g in gates):>5} {str(verdict):>8} "
              f"{matched:>7}/{len(orig):<6} {segs:>9} {longest:>8}   {' '.join(names)}")
        json.dump({"name": f"tzap{level}", "gates": gates}, open(out / f"tzap{level}.json", "w"))


if __name__ == "__main__":
    main()
