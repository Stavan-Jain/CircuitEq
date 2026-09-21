#!/usr/bin/env python3
"""Equivalence pairs and optimisation baselines from the circuit catalogue.

A pair is a catalogue circuit (``scripts/circuit_sources.py``) and a twin of
it, written as the JSON that ``scripts/agent_harness.py import-pair`` reads.
Three kinds of twin:

* ``peephole``: the pass of ``scripts/peephole_pairs.py`` (the library's own
  commutation and cancellation rules plus one-wire phase fusions), exact by
  construction;
* ``pyzx_teleport`` and ``pyzx_full_reduce``: the two pipelines of
  ``scripts/check_pyzx_benchmarks.py`` (pyzx 0.9.0), run in a child process
  under a time limit. ``Y`` is handed to PyZX as ``Sdg; X; S``;
* ``nam_light``, ``nam_heavy``, ``tpar``, ``pyzx_published``: optimiser
  outputs published for the Feynman suite and kept in the PyZX repository,
  paired with the catalogue's copy of the same circuit after checking that the
  published input is that circuit, gate for gate.

For every pair the script records what an agent is up against, the way
``benchmarks/harness/notes/distance.py`` and ``optimisers.py`` do: the
relation that actually holds (exact, up to a power of ``omega``, or neither;
numerically, so untrusted), gate, ``T``, ``H`` and ``CX`` counts, the share
of the original's gates that a diff matches in the raw order and after both
lists are put in one canonical order under ``Instr.CanCommute``, and the
number of segments and the longest segment between points where the two
prefix states agree up to a phase. The task's ``relation`` is set to what
holds: ``u``, or ``p`` with ``expected: equiv``; a pair that is not even
equal up to a phase becomes ``u`` with ``expected: not_equiv``.

Nothing here is trusted; the Lean kernel judges the pair.

Usage (the virtualenv Python has numpy and pyzx)::

    PY=/tmp/circuiteq-pyzx-venv/bin/python
    $PY scripts/circuit_pairs.py --self-test
    $PY scripts/circuit_pairs.py make feynman_tof_5 --twin pyzx_teleport
    $PY scripts/circuit_pairs.py batch            # the first batch, into benchmarks/circuits/pairs
    $PY scripts/circuit_pairs.py optimization     # benchmarks/circuits/optimization.json
    $PY scripts/circuit_pairs.py table            # the pairs as Markdown
"""

from __future__ import annotations

import argparse
import difflib
import heapq
import json
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import circuit_sources as cs  # noqa: E402

np = cs.np
PAIRS = cs.CATALOGUE / "pairs"
INDEX = PAIRS / "index.json"
OPTIMIZATION = cs.CATALOGUE / "optimization.json"

OWN_TWINS = ("peephole", "pyzx_teleport", "pyzx_full_reduce")
PUBLISHED_TWINS = {"nam_light": "nam_light", "nam_heavy": "nam_heavy", "tpar": "tpar",
                   "pyzx_published": "pyzx"}
# Twins whose gate lists may be copied into the repository: ours, and PyZX's
# own published outputs (Apache-2.0). The Nam et al. files have no licence
# upstream and T-par is a GPL-3.0 tool, so those pairs are written to the cache.
VENDORABLE = set(OWN_TWINS) | {"pyzx_published"}


def in_repo(circuit: str, kind: str) -> tuple[bool, str]:
    """Whether a pair is stored under ``benchmarks/circuits/pairs`` and, if not, why."""
    if kind not in VENDORABLE or circuit.startswith("published_"):
        return False, "the published file's source has no clear licence to redistribute"
    if kind in OWN_TWINS and circuit not in BATCH:
        return False, "not in the first batch; made for its T-count only"
    return True, ""

TWIN_TIMEOUT_S = 240       # each twin is made in a child process under this limit
PYZX_MAX_GATES = 8000      # hwb8 (18 220 gates) did not finish either pipeline in 200 s
DIFF_MAX_CELLS = 3e7       # len(a) * len(b) for difflib
SEGMENT_MAX_QUBITS = 20
SEGMENT_WORK = 2e10        # (len(a) + len(b)) * 2^n * probes
PROBES = 4
DIAG = {"Z", "S", "Sdg", "T", "Tdg"}

HOLDOUT_DELETE = ["scripts/circuit_pairs.py", "scripts/circuit_sources.py",
                  "scripts/peephole_pairs.py"]

# The first batch: circuits across the tiers that get our three twins.
BATCH = [
    # tier 1
    "feynman_tof_3", "feynman_tof_5", "feynman_mod5_4", "feynman_vbe_adder_3",
    "feynman_mod_mult_55", "feynman_qft_4", "qasmbench_adder_n10", "qasmbench_sat_n7",
    "gen_cuccaro_4", "qec_code_833_encode_basis",
    # tier 2
    "feynman_tof_10", "feynman_barenco_tof_10", "feynman_rc_adder_6", "feynman_gf2_4_mult",
    "feynman_hwb6", "feynman_ham15_low", "feynman_grover_5", "feynman_adder_8",
    "qasmbench_multiplier_n15", "qasmbench_qram_n20", "gen_cuccaro_8", "gen_surface_3",
    # tier 3
    "feynman_qcla_adder_10", "feynman_gf2_16_mult", "feynman_mod_adder_1024",
    "feynman_hwb8", "qasmbench_adder_n64", "gen_tof_50", "gen_surface_7",
]
# Published outputs are paired for every base of `cs.PUBLISHED_BASES`.

# The optimisation task's ladder: one or two rungs per family and tier. Every other
# T-bearing circuit of the catalogue is listed in `optimization.json` as well, unmarked.
RECOMMENDED = {
    "feynman_tof_3", "feynman_tof_5", "feynman_barenco_tof_4", "feynman_mod5_4",
    "feynman_vbe_adder_3", "feynman_mod_mult_55", "feynman_qft_4", "qasmbench_adder_n10",
    "qasmbench_sat_n7", "gen_cuccaro_4",
    "feynman_tof_10", "feynman_barenco_tof_10", "feynman_rc_adder_6", "feynman_adder_8",
    "feynman_qcla_com_7", "feynman_qcla_mod_7", "feynman_csla_mux_3", "feynman_csum_mux_9",
    "feynman_mod_red_21", "feynman_gf2_4_mult", "feynman_gf2_7_mult", "feynman_gf2_10_mult",
    "feynman_hwb6", "feynman_ham15_low", "feynman_ham15_med", "feynman_grover_5",
    "qasmbench_multiplier_n15", "qasmbench_qram_n20", "qasmbench_sat_n11",
    "qasmbench_adder_n28", "gen_cuccaro_14",
    "feynman_qcla_adder_10", "feynman_gf2_16_mult", "feynman_gf2_32_mult",
    "feynman_mod_adder_1024", "feynman_ham15_high", "feynman_hwb8", "qasmbench_adder_n64",
    "qasmbench_multiplier_n45", "qasmbench_multiplier_n75", "gen_tof_50",
    "gen_barenco_tof_50", "gen_cuccaro_49",
    "feynman_gf2_64_mult", "feynman_gf2_128_mult", "feynman_gf2_256_mult", "feynman_hwb10",
    "feynman_hwb12", "qasmbench_adder_n433", "qasmbench_multiplier_n400",
    "tzap_cobble_t_laplacian_filter", "tzap_cobble_t_ols_ridge", "tzap_qft_qft_q020_d32421",
    "tzap_qft_qft_q050_d87171", "gen_cuccaro_512",
}

# Imported as harness tasks (`import-pair`): a handful, one or two per tier.
HANDFUL = [
    "feynman_tof_5__pyzx_teleport",          # tier 1: phase folding on a kept skeleton
    "feynman_mod5_4__pyzx_full_reduce",      # tier 1: a re-synthesis, five qubits
    "qasmbench_adder_n10__peephole",         # tier 1: ten qubits, exact by construction
    "feynman_vbe_adder_3__pyzx_published",   # tier 1: a published output, 190 -> 115 gates
    "qasmbench_sat_n7__pyzx_teleport",       # tier 1: equal only up to -1, so `p`
    "feynman_rc_adder_6__pyzx_teleport",     # tier 2: 14 qubits
    "feynman_gf2_4_mult__pyzx_published",    # tier 2: 12 qubits, published
    "feynman_grover_5__peephole",            # tier 2: 1023 gates on 9 qubits
    "gen_tof_50__pyzx_teleport",             # tier 3: 99 qubits, width rather than depth
    "feynman_hwb8__peephole",                # tier 3: 18 220 gates on 12 qubits
]


# --------------------------------------------------------------------------
# Twins
# --------------------------------------------------------------------------

def peephole_twin(strings: list[str]) -> tuple[list[str], dict]:
    from certificate import cnot, fmt_instr, one
    import peephole_pairs
    circuit = [cnot(*w) if name == "CX" else one(name, w[0])
               for name, w in cs.parse_gates(strings)]
    twin, rewrites = peephole_pairs.peephole(circuit)
    return [fmt_instr(g) for g in twin], {"rewrites": rewrites}


def to_pyzx(strings: list[str], n: int):
    """The gate strings as a PyZX circuit; ``Y = S X Sdg`` exactly."""
    import pyzx as zx
    from fractions import Fraction
    quarter = {"T": 1, "S": 2, "Z": 4, "Sdg": 6, "Tdg": 7}
    c = zx.Circuit(n)
    for name, w in cs.parse_gates(strings):
        if name == "CX":
            c.add_gate("CNOT", w[0], w[1])
        elif name == "H":
            c.add_gate("HAD", w[0])
        elif name == "X":
            c.add_gate("NOT", w[0])
        elif name == "Y":
            c.add_gate("ZPhase", w[0], phase=Fraction(6, 4))
            c.add_gate("NOT", w[0])
            c.add_gate("ZPhase", w[0], phase=Fraction(2, 4))
        else:
            c.add_gate("ZPhase", w[0], phase=Fraction(quarter[name], 4))
    return c


def pyzx_twin(strings: list[str], n: int, pipeline: str) -> tuple[list[str], dict]:
    import pyzx as zx
    import check_pyzx_benchmarks as cpb
    out = cpb.optimize(to_pyzx(strings, n), pipeline)
    return cpb.lean_instructions(out), {"pyzx": zx.__version__}


def twin_worker(kind: str, src: str, dst: str) -> None:
    """Child process: make one twin and write it with the tool's own account."""
    data = json.loads(Path(src).read_text())
    t0 = time.time()
    if kind == "peephole":
        gates, info = peephole_twin(data["gates"])
    else:
        gates, info = pyzx_twin(data["gates"], data["qubits"], kind.removeprefix("pyzx_"))
    Path(dst).write_text(json.dumps({"gates": gates,
                                     "info": {**info, "seconds": round(time.time() - t0, 2)}}))


TOOLS = {"peephole": "scripts/peephole_pairs.py peephole",
         "pyzx_teleport": "pyzx teleport_reduce + basic_optimization "
                          "(scripts/check_pyzx_benchmarks.py optimize)",
         "pyzx_full_reduce": "pyzx full_reduce + extract_circuit + basic_optimization "
                             "(scripts/check_pyzx_benchmarks.py optimize)"}


def own_twin(kind: str, strings: list[str], n: int,
             timeout: float = TWIN_TIMEOUT_S) -> tuple[list[str] | None, dict]:
    """A twin made here, in a child process that is stopped at the time limit."""
    tool = {"tool": TOOLS[kind]}
    if kind != "peephole" and len(strings) > PYZX_MAX_GATES:
        return None, {**tool, "status": f"skipped: {len(strings)} gates is past the bound of "
                                        f"{PYZX_MAX_GATES} for a {timeout:.0f} s PyZX run"}
    (cs.cache_dir() / "tmp").mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=cs.cache_dir() / "tmp") as d:
        src, dst = Path(d) / "in.json", Path(d) / "out.json"
        src.write_text(json.dumps({"qubits": n, "gates": strings}))
        try:
            p = subprocess.run([sys.executable, __file__, "_twin", kind, str(src), str(dst)],
                               capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, {**tool, "status": f"stopped after {timeout:.0f} s"}
        if p.returncode != 0 or not dst.exists():
            last = (p.stderr.strip().splitlines() or ["no output"])[-1]
            return None, {**tool, "status": "failed: " + last[:200]}
        out = json.loads(dst.read_text())
    return out["gates"], {**tool, **out["info"]}


# --------------------------------------------------------------------------
# The published outputs: is the published input our circuit?
# --------------------------------------------------------------------------

_DIAGONAL_OPS = {"z", "s", "sdg", "t", "tdg", "phase", "cz", "ccz"}


def op_wire_type(op: tuple, w: int):
    """`wire_type` for native operations: diagonal, X-like, or only equal to itself."""
    name = op[0]
    if name in _DIAGONAL_OPS or (name == "cx" and op[1][0] == w):
        return "D"
    return "X" if name in ("x", "cx") else op


def normal_ops(ops: list[tuple]) -> list[tuple]:
    """A normal form of a native operation list under three sound rewrites: a Toffoli is
    ``h; ccz; h`` (and ``ccz``, ``cz`` are symmetric), two Hadamards next to each other on a
    wire cancel, and operations that are both diagonal or both X-like on every shared wire
    commute. Equal normal forms mean the same circuit, syntactically."""
    out: list[tuple | None] = []
    on_wire: dict[int, list[int]] = {}
    for op in ops:
        name, w = op[0], op[1]
        if name == "ccx":
            parts = [("h", (w[2],)), ("ccz", tuple(sorted(w))), ("h", (w[2],))]
        elif name in ("ccz", "ccz_dg", "cz"):
            parts = [(name.removesuffix("_dg"), tuple(sorted(w)))]
        else:
            parts = [op]
        for p in parts:
            stack = on_wire.setdefault(p[1][0], [])
            if p[0] == "h" and stack and out[stack[-1]] == p:
                out[stack.pop()] = None
                continue
            for x in p[1]:
                on_wire.setdefault(x, []).append(len(out))
            out.append(p)
    kept = [p for p in out if p is not None]
    return [kept[i] for i in canonical_order(kept, op_wire_type)]


def published_base(name: str) -> str | None:
    """`feynman_gf2_4_mult` or `published_gf2_4_mult__before` -> `gf2^4_mult`, when that base
    has published outputs."""
    for base in cs.PUBLISHED_BASES:
        if name in ("feynman_" + cs._clean(base), f"published_{cs._clean(base)}__before"):
            return base
    return None


def same_as_published_input(name: str, base: str, hashes: dict) -> tuple[bool, str]:
    ours, _ = cs.load_ops(cs.find_spec(name), hashes)
    theirs, _ = cs.load_ops(cs.published_spec(base, "before"), hashes)
    if ours["qubits"] != theirs["qubits"]:
        return False, f"{ours['qubits']} against {theirs['qubits']} qubits"
    if normal_ops(ours["ops"]) == normal_ops(theirs["ops"]):
        return True, "the published input is this circuit: equal normal forms (Toffoli as " \
                     "H; CCZ; H, H pairs cancelled, commuting operations ordered)"
    res = cs.compare_lists(ours["ops"], theirs["ops"], ours["qubits"])
    return res["relation"] == "exact", f"numerically {res['relation']} ({res['method']})"


# --------------------------------------------------------------------------
# Difficulty metadata
# --------------------------------------------------------------------------

def wire_type(g: tuple, w: int) -> str:
    """How a gate acts on one of its wires, for `Instr.CanCommute`: two gates commute iff
    they have the same type on every wire they share."""
    name, wires = g
    if name == "CX":
        return "D" if wires[0] == w else "X"
    return "D" if name in DIAG else name  # "X", "H", "Y"


def can_commute(a: tuple, b: tuple) -> bool:
    return all(wire_type(a, w) == wire_type(b, w) for w in a[1] if w in b[1])


def canonical_order(gates: list[tuple], wire_type=None) -> list[int]:
    """``tcount_survey.canonical_order(gates, "greedy/cancommute")``, in near-linear time.

    On one wire the gates fall into runs of one type, and everything in an
    earlier run precedes everything in a later one; edges from the previous
    run alone have the same transitive closure as all non-commuting pairs, and
    a priority topological sort depends only on the closure.
    """
    wire_type = wire_type or globals()["wire_type"]
    n = len(gates)
    indeg, succs = [0] * n, [[] for _ in range(n)]
    runs: dict[int, list] = {}  # wire -> [type, current run, previous run]
    for j, g in enumerate(gates):
        preds = set()
        for w in g[1]:
            t, run = wire_type(g, w), runs.get(w)
            if run is None:
                runs[w] = [t, [j], []]
            elif run[0] == t:
                preds.update(run[2])
                run[1].append(j)
            else:
                preds.update(run[1])
                runs[w] = [t, [j], run[1]]
        indeg[j] = len(preds)
        for i in preds:
            succs[i].append(j)
    key = lambda i: ((min(gates[i][1]), gates[i][0], gates[i][1:]), i)  # noqa: E731
    heap = [key(i) for i in range(n) if indeg[i] == 0]
    heapq.heapify(heap)
    order = []
    while heap:
        _, i = heapq.heappop(heap)
        order.append(i)
        for j in succs[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                heapq.heappush(heap, key(j))
    return order


def ordered(gates: list[tuple], how: str) -> list[tuple]:
    return gates if how == "raw" else [gates[i] for i in canonical_order(gates)]


def diff_matched(a: list[tuple], b: list[tuple]) -> dict:
    if len(a) * len(b) > DIFF_MAX_CELLS:
        return {"skipped": f"{len(a)} x {len(b)} gates is past the diff's budget"}
    sm = difflib.SequenceMatcher(None, [cs.show(g) for g in a], [cs.show(g) for g in b],
                                 autojunk=False)
    matched = sum(m.size for m in sm.get_matching_blocks())
    return {"matched": matched, "of": len(a),
            "fraction": round(matched / len(a), 4) if a else 1.0}


def signatures(gates: list[tuple], state, probes):
    """``|<probe_k | prefix_i>|`` for every prefix: equal rows mean, up to chance, prefix
    states equal up to a phase, without keeping the states."""
    flat = state.reshape(-1)
    sig = np.empty((len(gates) + 1, len(probes)))
    sig[0] = np.abs(probes @ flat)
    for k, g in enumerate(gates):
        cs.apply_op(state, g)
        sig[k + 1] = np.abs(probes @ flat)
    return sig


def segments(a: list[tuple], b: list[tuple], n: int) -> dict:
    """The greedy chain of `distance.py`: cut where the prefix states agree up to a phase."""
    if n > SEGMENT_MAX_QUBITS or (len(a) + len(b)) * 2 ** n * PROBES > SEGMENT_WORK:
        return {"skipped": f"{n} qubits and {len(a) + len(b)} gates are past the budget for "
                           "prefix states"}
    rng = np.random.default_rng(1)
    psi = cs.random_states(n, 1, 1)
    probes = (rng.normal(size=(PROBES, 2 ** n)) + 1j * rng.normal(size=(PROBES, 2 ** n))).conj()
    sa, sb = signatures(a, psi.copy(), probes), signatures(b, psi.copy(), probes)
    cuts, j0 = [(0, 0)], 0
    for i in range(1, len(sa)):
        rest = sb[j0 + 1:]
        hit = np.nonzero(np.abs(rest[:, 0] - sa[i, 0]) < 1e-8)[0]
        hit = [j for j in hit if np.all(np.abs(rest[j] - sa[i]) < 1e-8)]
        if hit:
            j0 += 1 + int(hit[0])
            cuts.append((i, j0))
    if cuts[-1] != (len(a), len(b)):
        cuts.append((len(a), len(b)))
    gaps = [(c2[0] - c1[0]) + (c2[1] - c1[1]) for c1, c2 in zip(cuts, cuts[1:])]
    return {"segments": len(gaps), "longest": max(gaps)}


def describe(original: list[str], twin: list[str], n: int) -> dict:
    a, b = cs.parse_gates(original), cs.parse_gates(twin)
    meta = {"relation_found": cs.compare_lists(a, b, n),
            **{k: [cs.counts(a)[k], cs.counts(b)[k]]
               for k in ("gates", "t_count", "h_count", "cx_count")},
            "fragment": [cs.fragment(a), cs.fragment(b)], "diff_matched": {}, "segments": {}}
    for how in ("raw", "greedy/cancommute"):
        x, y = ordered(a, how), ordered(b, how)
        meta["diff_matched"][how] = diff_matched(x, y)
        meta["segments"][how] = segments(x, y, n)
    return meta


# --------------------------------------------------------------------------
# Pairs
# --------------------------------------------------------------------------

def known_leaks(circuit: str) -> list[str]:
    leaks = {
        "feynman_tof_3": "the repository proves `tof_3` (the same three Toffolis on other "
                         "wires, without the H pairs) against PyZX teleport",
        "feynman_barenco_tof_3": "the repository proves `barenco_tof_3` (generator layout)",
        "gen_tof_3": "this is the promoted benchmark `tof_3`",
        "gen_barenco_tof_3": "this is the promoted benchmark `barenco_tof_3`",
        "qec_rep3_phaseflip_encode": "a promoted benchmark",
        "qec_steane_713_encode_plusL": "a promoted benchmark",
        "qec_rm15_1531_encode_0L": "a promoted benchmark",
    }
    return [leaks[circuit]] if circuit in leaks else []


def make_pair(circuit: str, kind: str, hashes: dict) -> dict:
    """One pair as a dictionary; ``status`` says why there is none."""
    rec, original = cs.build(cs.find_spec(circuit), hashes, check=False, cross=False)
    n = rec["qubits"]
    base = {"name": f"{circuit}__{kind}", "circuit": circuit, "twin": kind, "qubits": n,
            "tier": rec["tier"], "in_repo": in_repo(circuit, kind)[0]}
    if not base["in_repo"]:
        base["why_not_in_repo"] = in_repo(circuit, kind)[1]
    if kind in OWN_TWINS:
        twin, tool = own_twin(kind, original, n)
        if twin is None:
            return {**base, "status": tool["status"], "tool": tool}
    elif kind in PUBLISHED_TWINS:
        pub = published_base(circuit)
        if pub is None:
            return {**base, "status": "skipped: no published output for this circuit"}
        if circuit.startswith("published_"):
            same, how = True, "the original is the published input itself"
        else:
            same, how = same_as_published_input(circuit, pub, hashes)
        if not same:
            return {**base, "status": f"skipped: the published input is not this circuit: {how}"}
        spec = cs.published_spec(pub, PUBLISHED_TWINS[kind])
        try:
            prec, twin = cs.build(spec, hashes, check=False, cross=False)
        except (cs.Rejected, subprocess.CalledProcessError) as e:
            return {**base, "status": f"skipped: {e}"}
        s = cs.SOURCES["pyzx_repo"]
        tool = {"tool": spec["note"], "url": s["url"], "commit": s["commit"],
                "path": spec["path"], "sha256": prec["sha256"], "licence": s["licence"],
                "input_check": how, "notes": prec["notes"]}
        zero = cs.load_ops(spec, hashes)[0].get("zero_wires", [])
    else:
        raise ValueError(kind)
    meta = describe(original, twin, n)
    found = meta["relation_found"]["relation"]
    if found == "different" and kind in PUBLISHED_TWINS and zero:
        # the tool read a .qc file that marks these wires as ancillas starting in |0>
        meta["relation_on_clean_ancillas"] = {"zero_wires": zero, **cs.compare_lists(
            cs.parse_gates(original), cs.parse_gates(twin), n, zero_wires=tuple(zero))}
    relation, expected = {"exact": ("u", "equiv"), "phase": ("p", "equiv"),
                          "different": ("u", "not_equiv"),
                          "unchecked": ("p", "unknown")}[found]
    if found == "unchecked" and kind == "peephole":
        relation, expected = "u", "equiv"  # exact by construction, not checked numerically
    pair = {
        "name": base["name"], "qubits": n, "relation": relation, "expected": expected,
        "split": "held-out", "family": rec["family"], "rung": rec["size"],
        "original": original, "optimized": twin,
        # `optimiser` is the name `optimizer_harness.py import-pair` files the twin under
        "source": {"generator": "scripts/circuit_pairs.py", "optimiser": kind,
                   "circuit": circuit,
                   "circuit_source": {k: rec.get(k) for k in ("source", "path", "sha256")},
                   "circuit_licence": cs.SOURCES[rec["source"]]["licence"],
                   "twin": kind, "twin_tool": tool, "tier": rec["tier"], **meta},
        "holdout_delete": HOLDOUT_DELETE, "known_leaks": known_leaks(circuit),
    }
    return {**base, "status": "ok", "pair": pair}


def summary(result: dict) -> dict:
    """The index row of a pair: everything but the gate lists."""
    row = {k: result[k] for k in ("name", "circuit", "twin", "qubits", "tier", "in_repo",
                                  "why_not_in_repo", "status") if k in result}
    if result["status"] == "ok":
        p = result["pair"]
        row.update(relation=p["relation"], expected=p["expected"],
                   **{k: v for k, v in p["source"].items()
                      if k in ("relation_found", "relation_on_clean_ancillas", "gates",
                               "t_count", "h_count", "cx_count", "fragment", "diff_matched",
                               "segments", "twin_tool")})
    elif "tool" in result:
        row["twin_tool"] = result["tool"]
    return row


def write_pair(result: dict, out: Path | None = None) -> Path | None:
    if result["status"] != "ok":
        return None
    d = out or (PAIRS if result["in_repo"] else cs.cache_dir() / "pairs")
    d.mkdir(parents=True, exist_ok=True)
    path = d / f"{result['name']}.json"
    pair = result["pair"]
    head = {k: v for k, v in pair.items() if k not in ("original", "optimized")}
    text = json.dumps(head, indent=1, ensure_ascii=False)[:-2] + ",\n" + \
        f' "original": {json.dumps(pair["original"])},\n' + \
        f' "optimized": {json.dumps(pair["optimized"])}\n}}\n'
    path.write_text(text)
    return path


def load_index() -> dict:
    return json.loads(INDEX.read_text()) if INDEX.exists() else {"pairs": []}


def save_index(index: dict) -> None:
    PAIRS.mkdir(parents=True, exist_ok=True)
    index["pairs"].sort(key=lambda r: (r["tier"], r["circuit"], r["twin"]))
    index["generated_by"] = "scripts/circuit_pairs.py batch"
    index["note"] = ("One row per pair made so far. Pairs with `in_repo: false` are written "
                     "to ~/.circuiteq-harness/circuit-cache/pairs/ and not to the repository; "
                     "`why_not_in_repo` says why. `scripts/circuit_pairs.py make CIRCUIT --twin "
                     "KIND` remakes any of them.")
    INDEX.write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n")


def cmd_make(args) -> None:
    hashes = cs.recorded_hashes(cs.load_manifest())
    index = load_index()
    for circuit in args.circuits:
        for kind in args.twin:
            t0 = time.time()
            result = make_pair(circuit, kind, hashes)
            path = write_pair(result, args.out)
            index["pairs"] = [r for r in index["pairs"] if r["name"] != result["name"]]
            index["pairs"].append(summary(result))
            if not args.out:
                save_index(index)
            print(f"{result['name']}: {result['status']} "
                  f"{path if path else ''} ({time.time() - t0:.0f} s)", flush=True)


def cmd_batch(args) -> None:
    hashes = cs.recorded_hashes(cs.load_manifest())
    index = load_index()
    done = {r["name"] for r in index["pairs"]} if not args.force else set()
    jobs = [(c, k) for c in BATCH for k in OWN_TWINS]
    jobs += [("feynman_" + cs._clean(b), k) for b in cs.PUBLISHED_BASES for k in PUBLISHED_TWINS]
    if args.tcounts:  # PyZX on every other T-bearing circuit it can take, smallest first
        rest = sorted((r for r in cs.load_manifest()["circuits"]
                       if r["t_count"] and r["name"] not in BATCH
                       and (r["tier"] <= 3 or r["gates"] <= PYZX_MAX_GATES)),
                      key=lambda r: r["gates"])
        jobs += [(r["name"], k) for r in rest for k in OWN_TWINS[1:]]
    deadline = time.time() + args.minutes * 60
    for circuit, kind in jobs:
        name = f"{circuit}__{kind}"
        if name in done or (args.only and not any(name.startswith(p) for p in args.only)):
            continue
        if time.time() > deadline:
            print(f"stopping at the {args.minutes}-minute limit; run `batch` again to continue")
            break
        t0 = time.time()
        result = make_pair(circuit, kind, hashes)
        write_pair(result)
        index["pairs"] = [r for r in index["pairs"] if r["name"] != name] + [summary(result)]
        save_index(index)
        rel = result.get("pair", {}).get("source", {}).get("relation_found", {})
        print(f"{name}: {result['status']} {rel.get('relation', '')} "
              f"({time.time() - t0:.0f} s)", flush=True)


# --------------------------------------------------------------------------
# The optimisation task: what uncertified tools reach
# --------------------------------------------------------------------------

def optimization_table() -> str:
    """The recommended ladder of `optimization.json` as Markdown."""
    data = json.loads(OPTIMIZATION.read_text())
    kinds = ("pyzx_teleport", "pyzx_full_reduce", "nam_heavy", "tpar", "pyzx_published")
    out = ["| Circuit | Tier | Qubits | Gates | T | PyZX teleport | PyZX full_reduce | "
           "Nam heavy | T-par | PyZX published | TZAP |", "|---|---:|" + "---:|" * 9]
    for tier in sorted(k for k in data if k.startswith("tier_")):
        for e in data[tier]:
            if not e["recommended"]:
                continue
            cells = []
            for k in kinds:
                t = e["tools"].get(k)
                if t is None:
                    cells.append("")
                elif "t_count" not in t:
                    cells.append("—")
                else:
                    flag = "\\*" if t["relation_to_source"] == "different" else ""
                    cells.append(f"{t['t_count']}{flag}")
            out.append(f"| `{e['name']}` | {tier[-1]} | {e['qubits']} | {e['gates']} | "
                       f"{e['t_count']} | " + " | ".join(cells) + " | |")
    return "\n".join(out)


def cmd_optimization(args) -> None:
    """Every T-bearing circuit of the catalogue, by tier, with the T-count each external tool
    reaches on it (from the pairs index; nothing is recomputed here)."""
    if args.table or args.readme:
        if args.readme:
            cs.replace_block(cs.CATALOGUE / "README.md", "OPTIMISATION TABLE",
                             optimization_table())
        else:
            print(optimization_table())
        return
    manifest = cs.load_manifest()
    rows = {r["name"]: r for r in load_index()["pairs"]}
    tiers: dict[str, list] = {}
    for rec in manifest["circuits"]:
        if rec["t_count"] == 0:
            continue
        tools = {}
        for kind in OWN_TWINS[1:] + tuple(PUBLISHED_TWINS):
            row = rows.get(f"{rec['name']}__{kind}")
            if row is None:
                if kind in OWN_TWINS:
                    tools[kind] = {"status": "not run" + (" at this size" if rec["tier"] == 4
                                                           else "")}
                continue
            if row["status"] != "ok":
                if kind in OWN_TWINS:
                    tools[kind] = {"status": row["status"]}
                continue
            tools[kind] = {"t_count": row["t_count"][1], "gates": row["gates"][1],
                           "cx_count": row["cx_count"][1],
                           "relation_to_source": row["relation_found"]["relation"]}
            if "seconds" in row.get("twin_tool", {}):
                tools[kind]["seconds"] = row["twin_tool"]["seconds"]
        known = [t["t_count"] for t in tools.values() if "t_count" in t
                 and t["relation_to_source"] in ("exact", "phase", "unchecked")]
        entry = {"name": rec["name"], "recommended": rec["name"] in RECOMMENDED,
                 "family": rec["family"], "size": rec["size"], "qubits": rec["qubits"],
                 "gates": rec["gates"], "t_count": rec["t_count"], "cx_count": rec["cx_count"],
                 "fragment": rec["fragment"], "source": rec["source"],
                 "translated_sha256": rec["translated_sha256"],
                 "best_uncertified_t_count": min(known) if known else None,
                 "tools": {**tools, "tzap": None}}
        tiers.setdefault(f"tier_{rec['tier']}", []).append(entry)
    for entries in tiers.values():
        entries.sort(key=lambda e: (e["gates"], e["name"]))
    out = {
        "generated_by": "scripts/circuit_pairs.py optimization",
        "task": "Given the source circuit, produce a cheaper circuit (T-count first, then "
                "gates) with a Lean proof of equivalence. The numbers are what uncertified "
                "tools reach on the same gate list; `best_uncertified_t_count` counts only "
                "outputs that were not found to differ from the source.",
        "how_to_get_a_circuit": "scripts/circuit_sources.py translate NAME --out DIR; compare "
                                "`translated_sha256`",
        "recommended": "the ladder to report on: one or two rungs per family and tier; the "
                       "other entries are the rest of the catalogue's T-bearing circuits",
        "tools": {
            "pyzx_teleport": "pyzx 0.9.0 teleport_reduce + basic_optimization, run here "
                             f"(limit {TWIN_TIMEOUT_S} s and {PYZX_MAX_GATES} gates)",
            "pyzx_full_reduce": "pyzx 0.9.0 full_reduce + extract_circuit + "
                                "basic_optimization, run here (same limits)",
            "nam_light, nam_heavy": "published outputs of Nam, Ross, Su, Childs, Maslov "
                                    "(arXiv:1710.07345), from the PyZX repository",
            "tpar": "published T-par outputs, from the PyZX repository; T-par may assume that "
                    "ancillas start in |0>, see `relation_to_source`",
            "pyzx_published": "PyZX's published outputs (arXiv:1903.10477), which add phase "
                              "gadget optimisation (TODD) on some circuits",
            "tzap": "to be filled in; TZAP is being installed separately. Its benchmark copy "
                    "of the Feynman suite is these gate lists exactly",
        },
        **dict(sorted(tiers.items())),
    }
    OPTIMIZATION.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print(f"wrote {OPTIMIZATION.relative_to(ROOT)}: "
          + ", ".join(f"{k}: {len(v)} ({sum(e['recommended'] for e in v)} recommended)"
                      for k, v in sorted(tiers.items())))


def cmd_handful(args) -> None:
    """The `import-pair` commands for the handful of harness tasks; `--run` runs them."""
    for name in HANDFUL:
        path = PAIRS / f"{name}.json"
        cmd = [sys.executable if args.run else "python3", "scripts/agent_harness.py",
               "import-pair", str(path.relative_to(ROOT))]
        if not path.exists():
            print(f"# missing: {path.relative_to(ROOT)} (run `batch` first)")
        elif args.run:
            p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
            print((p.stdout + p.stderr).strip())
        else:
            print(" ".join(cmd))


PAIRS_README = """\
# Pairs made from the circuit catalogue

Generated by `scripts/circuit_pairs.py table --write` from `index.json`; the
catalogue's `README.md` says what the pairs are and what was found. One row
per pair made so far.

- **Holds**: what a numerical comparison finds, so an untrusted oracle:
  `exact`, `phase (ω^k)` (the twin is `ω^k` times the original), `different`,
  or `unchecked`. `sampled` marks a sparse simulation on sixteen random basis
  inputs (wide registers) instead of full unitaries or random states. The
  task's `relation` is `u` for `exact`, `p` for `phase`, and `u` with
  `expected: not_equiv` for `different`.
- **Diff raw / canonical**: the share of the original's gates that
  `difflib` matches against the twin, on the lists as they are and after both
  are put in one canonical order under `Instr.CanCommute`.
- **Segments / Longest**: the number of segments between points where the two
  prefix states agree up to a phase, and the longest segment in gates (both
  sides added), in the canonical order; `raw` is in `index.json`. One segment
  means the pair cannot be cut anywhere; `—` means the register is past 20
  qubits or the work past the budget, so prefix states were not computed.
- **In repo**: `no` means the pair is written to
  `~/.circuiteq-harness/circuit-cache/pairs/`, because the twin's source has
  no clear licence to redistribute or because the pair was made for its
  T-count only; `index.json` says which.

"""


def table_rows(rows: list[dict]) -> list[str]:
    out = ["| Pair | Tier | Qubits | Gates | T | Holds | Diff raw | Diff canonical | Segments | "
           "Longest | In repo |", "|---|---:|---:|---:|---:|---|---:|---:|---:|---:|---|"]
    for r in rows:
        if r["status"] != "ok":
            out.append(f"| `{r['name']}` | {r['tier']} | {r['qubits']} | — | — | "
                       f"{r['status']} | — | — | — | — | — |")
            continue
        rel = r["relation_found"]
        holds = rel["relation"] + (f" (ω^{rel['omega_power']})" if "omega_power" in rel else "")
        if rel["method"].startswith("sparse"):
            holds += ", sampled"
        clean = r.get("relation_on_clean_ancillas")
        if clean:
            holds += f"; {clean['relation']} on clean ancillas"
        d, seg = r["diff_matched"], r["segments"]["greedy/cancommute"]
        frac = lambda x: f"{x['fraction']:.2f}" if "fraction" in x else "—"  # noqa: E731
        out.append(f"| `{r['name']}` | {r['tier']} | {r['qubits']} | {r['gates'][0]} → "
                   f"{r['gates'][1]} | {r['t_count'][0]} → {r['t_count'][1]} | {holds} | "
                   f"{frac(d['raw'])} | {frac(d['greedy/cancommute'])} | "
                   f"{seg.get('segments', '—')} | {seg.get('longest', '—')} | "
                   f"{'yes' if r['in_repo'] else 'no'} |")
    return out


def cmd_table(args) -> None:
    rows = load_index()["pairs"]
    if args.only:
        rows = [r for r in rows if any(r["name"].startswith(p) for p in args.only)]
    text = "\n".join(table_rows(rows))
    if args.write:
        (PAIRS / "README.md").write_text(PAIRS_README + text + "\n")
        print(f"wrote {(PAIRS / 'README.md').relative_to(ROOT)}: {len(rows)} rows")
    else:
        print(text)


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------

def self_test() -> None:
    rng = random.Random(3)
    names = ["H", "X", "Y", "Z", "S", "Sdg", "T", "Tdg"]

    def rand(n, k):
        out = []
        for _ in range(k):
            if rng.random() < 0.4:
                out.append(("CX", tuple(rng.sample(range(n), 2))))
            else:
                out.append((rng.choice(names), (rng.randrange(n),)))
        return out

    try:
        import tcount_survey as ts
    except ImportError:
        ts = None
        print("(pyzx not importable: skipped the comparison with tcount_survey.py)")
    for n, k in ((2, 40), (3, 120), (6, 300)):
        gates = rand(n, k)
        if ts:
            for a in gates[:40]:
                for b in gates[:40]:
                    assert can_commute(a, b) == ts.can_commute(a, b), (a, b)
            assert canonical_order(gates) == ts.canonical_order(gates, "greedy/cancommute")
        order = canonical_order(gates)
        assert sorted(order) == list(range(k))
        res = cs.compare_lists(gates, [gates[i] for i in order], n)
        assert res["relation"] == "exact", res

    strings = [cs.show(g) for g in rand(5, 200)]
    twin, tool = own_twin("peephole", strings, 5)
    assert len(twin) < len(strings) and tool["rewrites"] > 0 and "seconds" in tool
    assert own_twin("pyzx_teleport", ["H 0"] * (PYZX_MAX_GATES + 1), 1)[0] is None
    meta = describe(strings, twin, 5)
    assert meta["relation_found"]["relation"] == "exact"
    assert meta["segments"]["raw"]["segments"] > 1
    assert meta["diff_matched"]["raw"]["of"] == 200
    # the same segmentation as distance.py computes from whole prefix states
    a, b = cs.parse_gates(strings), cs.parse_gates(twin)
    psi = cs.random_states(5, 1, 1)

    def prefixes(gs):
        s, out = psi.copy(), [psi.reshape(-1).copy()]
        for g in gs:
            cs.apply_op(s, g)
            out.append(s.reshape(-1).copy())
        return np.array(out)

    ok = np.abs(prefixes(a).conj() @ prefixes(b).T) > 1 - 1e-9
    cuts, j0 = [(0, 0)], 0
    for i in range(1, len(a) + 1):
        js = np.nonzero(ok[i, j0 + 1:])[0]
        if len(js):
            j0 += 1 + js[0]
            cuts.append((i, j0))
    gaps = [(c2[0] - c1[0]) + (c2[1] - c1[1]) for c1, c2 in zip(cuts, cuts[1:])]
    assert meta["segments"]["raw"] == {"segments": len(gaps), "longest": max(gaps)}

    # a mutant is found different, a global phase is found as a phase
    assert describe(strings, twin[:-1], 5)["relation_found"]["relation"] == "different"
    phase = describe(["X 0", "Z 0", "X 0", "Z 0", "H 1"], ["H 1"], 2)["relation_found"]
    assert phase["relation"] == "phase" and phase["omega_power"] == 4
    # Feynman's .qasm writes `H; Z a b c; H` of the .qc as `h; h; ccx; h; h`
    assert normal_ops([("h", (2,)), ("h", (2,)), ("ccx", (0, 1, 2)), ("h", (2,)), ("h", (2,))]) \
        == normal_ops([("h", (2,)), ("ccz", (1, 0, 2)), ("h", (2,))]) \
        == [("h", (2,)), ("ccz", (0, 1, 2)), ("h", (2,))]
    assert normal_ops([("h", (2,)), ("ccx", (0, 1, 2)), ("h", (2,))]) == [("ccz", (0, 1, 2))]
    # Hadamards cancel across gates on other wires; diagonal operations are reordered
    assert normal_ops([("h", (2,)), ("t", (0,)), ("h", (2,)), ("ccz", (0, 1, 2)), ("cx", (0, 3))]) \
        == normal_ops([("cx", (0, 3)), ("ccz", (2, 1, 0)), ("t", (0,))])
    assert normal_ops([("h", (0,)), ("t", (0,))]) != normal_ops([("t", (0,)), ("h", (0,))])
    if ts:
        import check_pyzx_benchmarks as cpb
        back = cpb.lean_instructions(to_pyzx(["Y 0", "T 1", "CX 0 1", "Sdg 1"], 2))
        assert back == ["Sdg 0", "X 0", "S 0", "T 1", "CX 0 1", "Sdg 1"], back
        assert cs.compare_lists(cs.parse_gates(back), cs.parse_gates(
            ["Y 0", "T 1", "CX 0 1", "Sdg 1"]), 2)["relation"] == "exact"
    print("self-test passed")


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1] == "_twin":
        twin_worker(*sys.argv[2:5])
        return
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--self-test", action="store_true")
    sub = parser.add_subparsers(dest="command")
    p = sub.add_parser("make", help="pairs for the named circuits")
    p.add_argument("circuits", nargs="+")
    p.add_argument("--twin", nargs="+", default=list(OWN_TWINS),
                   choices=list(OWN_TWINS) + list(PUBLISHED_TWINS))
    p.add_argument("--out", type=Path, help="write here and leave the index alone")
    p = sub.add_parser("batch", help="the first batch; resumes where it stopped")
    p.add_argument("--minutes", type=float, default=8, help="stop starting new pairs after this")
    p.add_argument("--only", nargs="*", help="pair-name prefixes")
    p.add_argument("--force", action="store_true", help="remake pairs already in the index")
    p.add_argument("--tcounts", action="store_true",
                   help="also run PyZX on the other T-bearing circuits of tiers 1 to 3")
    p = sub.add_parser("optimization", help="write optimization.json from the index")
    p.add_argument("--table", action="store_true", help="print its recommended ladder instead")
    p.add_argument("--readme", action="store_true",
                   help="put that table between the markers of the catalogue's README")
    p = sub.add_parser("table", help="the index as Markdown")
    p.add_argument("--write", action="store_true",
                   help="write benchmarks/circuits/pairs/README.md")
    p.add_argument("--only", nargs="*", help="pair-name prefixes")
    p = sub.add_parser("handful", help="print the import-pair commands of the harness tasks")
    p.add_argument("--run", action="store_true", help="run them")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.command == "make":
        cmd_make(args)
    elif args.command == "batch":
        cmd_batch(args)
    elif args.command == "optimization":
        cmd_optimization(args)
    elif args.command == "table":
        cmd_table(args)
    elif args.command == "handful":
        cmd_handful(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
