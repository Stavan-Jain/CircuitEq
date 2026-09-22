#!/usr/bin/env python3
"""The gate alphabet of the Lean library, once, for every Python script.

`Gate1` in `CircuitEq/Gates.lean` is `H X Y Z S Sdg T Tdg`, and an `Instr` is
one of those on a wire or a `CX`. The scripts that mirror, search, translate or
simulate circuits (`certificate.py`, `circuit_sources.py`, `circuit_pairs.py`,
`tcount_survey.py`, `peephole_pairs.py`, `check_pyzx_benchmarks.py`,
`scale_test.py`, `hard_pair.py`) import their tables from here, so a change to
the alphabet is one edit. Standard library only: numpy users build arrays from `MATRICES`.

`benchmarks/harness/tools/qasm.py` keeps its own copy of `TO_QASM` and `PHASES`,
because the harness copies it into a run workspace as a standalone executable;
`--self-test` checks that copy against this file, and checks this file against
`Gate1` and `Gate1.phase?` in the Lean sources.

Everything here is an untrusted mirror: nothing a script computes from these
tables is a proof.
"""
from __future__ import annotations

import ast
import cmath
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The single-qubit gates, in the order of `Gate1`'s constructors.
GATES = ("H", "X", "Y", "Z", "S", "Sdg", "T", "Tdg")
# The whole instruction alphabet: the single-qubit gates and the CNOT.
ALPHABET = GATES + ("CX",)
# The diagonal gates (`Gate1.isDiag`).
DIAG = frozenset({"Z", "S", "Sdg", "T", "Tdg"})
# The Clifford fragment (what the tableau checker covers).
CLIFFORD = frozenset({"H", "X", "Y", "Z", "S", "Sdg", "CX"})
# The CNOT-plus-diagonal fragment (what the phase polynomial covers).
CX_DIAGONAL = DIAG | {"CX"}
# `Gate1.inverse`.
INVERSE = {"H": "H", "X": "X", "Y": "Y", "Z": "Z", "S": "Sdg", "Sdg": "S", "T": "Tdg", "Tdg": "T"}

# A diagonal gate is `diag(1, ω^k)` with `ω = e^{iπ/4}`: its `k` (`Gate1.phase?`).
PHASE_OF_GATE = {"T": 1, "S": 2, "Z": 4, "Sdg": 6, "Tdg": 7}
# The diagonal gate of each phase, where there is one.
GATE_OF_PHASE = {k: g for g, k in PHASE_OF_GATE.items()}
# `diag(1, ω^k)` for every `k`, as gates of the alphabet in time order: the
# translation of `rz(k·π/4)` in PyZX's and TZAP's convention (`qelib1.inc`'s,
# not Qiskit's, which differs by a global phase).
PHASES = {0: [], 1: ["T"], 2: ["S"], 3: ["S", "T"], 4: ["Z"], 5: ["Z", "T"], 6: ["Sdg"],
          7: ["Tdg"]}

# OpenQASM 2 names (`qelib1.inc`). `y` is read but not written: TZAP has no `y`,
# so writers emit `sdg; x; s`, which is `Y` exactly.
TO_QASM = {"H": "h", "X": "x", "Z": "z", "S": "s", "Sdg": "sdg", "T": "t", "Tdg": "tdg"}
FROM_QASM = {v: k for k, v in TO_QASM.items()} | {"y": "Y"}
# The `k` of `diag(1, ω^k)` per diagonal gate, by its QASM name.
PHASE_OF = {TO_QASM[g]: k for g, k in PHASE_OF_GATE.items()}

# The matrices of `Gate1.mat`, row by row, as Python complex numbers.
_R = 1 / math.sqrt(2)
_W = cmath.exp(1j * math.pi / 4)
MATRICES = {
    "H": ((_R, _R), (_R, -_R)),
    "X": ((0, 1), (1, 0)),
    "Y": ((0, -1j), (1j, 0)),
    "Z": ((1, 0), (0, -1)),
    "S": ((1, 0), (0, 1j)),
    "Sdg": ((1, 0), (0, -1j)),
    "T": ((1, 0), (0, _W)),
    "Tdg": ((1, 0), (0, _W.conjugate())),
}


def _mat_mul(a, b):
    return tuple(tuple(sum(a[r][k] * b[k][c] for k in range(2)) for c in range(2))
                 for r in range(2))


def _close(a, b) -> bool:
    return all(abs(a[r][c] - b[r][c]) < 1e-12 for r in range(2) for c in range(2))


def self_test() -> None:
    """The tables agree with each other, with the Lean sources and with qasm.py."""
    ident = ((1, 0), (0, 1))
    assert set(INVERSE) == set(GATES) and all(INVERSE[INVERSE[g]] == g for g in GATES)
    for g in GATES:
        assert _close(_mat_mul(MATRICES[g], MATRICES[INVERSE[g]]), ident), g
    assert set(PHASE_OF_GATE) == DIAG
    for k, gates in PHASES.items():
        assert sum(PHASE_OF_GATE[g] for g in gates) % 8 == k, k
        m = ident
        for g in gates:
            m = _mat_mul(MATRICES[g], m)
        assert _close(m, ((1, 0), (0, _W ** k))), k
    for g, k in PHASE_OF_GATE.items():
        assert PHASES[k] == [g], g
    y = _mat_mul(MATRICES["S"], _mat_mul(MATRICES["X"], MATRICES["Sdg"]))
    assert _close(y, MATRICES["Y"]), "sdg; x; s is Y"

    gates_lean = (ROOT / "CircuitEq" / "Gates.lean").read_text()
    m = re.search(r"inductive Gate1 where\n\s*\|([^\n]*)", gates_lean)
    assert m and tuple(c.strip() for c in m[1].split("|")) == GATES, "Gate1's constructors"
    phase_lean = (ROOT / "CircuitEq" / "PhasePoly.lean").read_text()
    body = phase_lean[phase_lean.index("def Gate1.phase?"):]
    lean_phases = dict(re.findall(r"\| \.(\w+) => some (\d)", body[:body.index("\n\n")]))
    assert {g: int(k) for g, k in lean_phases.items()} == PHASE_OF_GATE, "Gate1.phase?"

    qasm = (ROOT / "benchmarks" / "harness" / "tools" / "qasm.py").read_text()
    copy = {}
    for name in ("TO_QASM", "PHASES"):
        line = re.search(rf"^{name} = (.*)$", qasm, re.M)
        assert line, f"qasm.py defines {name} as a literal on one line"
        copy[name] = ast.literal_eval(line[1])
    assert copy["TO_QASM"] == TO_QASM and copy["PHASES"] == PHASES, "qasm.py's copy"
    print("alphabet self-test passed")


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        self_test()
    else:
        sys.exit("usage: alphabet.py --self-test")
