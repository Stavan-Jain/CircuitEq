#!/usr/bin/env python3
"""Convert between the Lean circuit lists of a harness workspace and OpenQASM 2.

The harness copies this file into every run as `./qasm`, so that an external optimiser
(`./tzap`, PyZX under `./python`) can be used without each run rewriting a translator. It
needs only the standard library. Both directions are exact: nothing is approximated, and a
gate that cannot be written exactly is an error.

    ./qasm to-qasm Harness/Task.lean original > in.qasm     # a `def NAME : Circuit n := [...]`
    ./qasm to-lean out.qasm                                 # a Lean list, ready to paste
    ./qasm to-lean out.qasm --strings                       # one gate string per line
    ./qasm count out.qasm                                   # gates, T-count, CNOT count

Conventions. Lean gates are `H X Y Z S Sdg T Tdg` on a wire and `CX c t`. Towards QASM,
`Y q` is written `sdg q; x q; s q` (exactly `Y`, since several tools have no `y`). From
QASM, `cz a b` becomes `H b, CX a b, H b`; `rz(k*pi/4)` and `u1`/`p` of the same angles
become the diagonal gates with matrix `diag(1, e^{i k pi/4})` (`T`, `S`, `S T`, `Z`, ...),
which is OpenQASM 2's own `rz` of `qelib1.inc` and differs from Qiskit's `rz` by a global
phase; `y` and `id` are read too. Anything else (other angles, `ccx`, measurement) is
refused: decompose it first. An optimiser's output may equal its input only up to a global
phase; this tool does not check that, and nothing it prints is a proof.
"""
import argparse
import math
import re
import sys
from pathlib import Path

TO_QASM = {"H": "h", "X": "x", "Z": "z", "S": "s", "Sdg": "sdg", "T": "t", "Tdg": "tdg"}
FROM_QASM = {v: k for k, v in TO_QASM.items()} | {"y": "Y"}
PHASES = {0: [], 1: ["T"], 2: ["S"], 3: ["S", "T"], 4: ["Z"], 5: ["Z", "T"], 6: ["Sdg"], 7: ["Tdg"]}
GATE_RE = re.compile(r"^(?:(?:H|X|Y|Z|S|Sdg|T|Tdg) \d+|CX \d+ \d+)$")


def read_lean_def(path: Path, name: str) -> tuple[int, list[str]]:
    """The qubit count and gate strings of `def NAME : Circuit n := [...]` in a Lean file."""
    m = re.search(rf"def {re.escape(name)} : Circuit (\d+) :=\s*\[([^\]]*)\]", path.read_text())
    if m is None:
        sys.exit(f"{path}: no `def {name} : Circuit n := [...]` with a literal list")
    gates = [" ".join(g.split()) for g in m[2].split(",") if g.strip()]
    for g in gates:
        if not GATE_RE.match(g):
            sys.exit(f"{path}: cannot read the gate `{g}`")
    return int(m[1]), gates


def to_qasm(n: int, gates: list[str]) -> str:
    """The gate strings as an OpenQASM 2 program on one register `q`; `Y` as `sdg; x; s`."""
    out = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{n}];"]
    for g in gates:
        name, *w = g.split()
        if name == "CX":
            out.append(f"cx q[{w[0]}],q[{w[1]}];")
        elif name == "Y":
            out += [f"sdg q[{w[0]}];", f"x q[{w[0]}];", f"s q[{w[0]}];"]
        else:
            out.append(f"{TO_QASM[name]} q[{w[0]}];")
    return "\n".join(out) + "\n"


def eighth_turns(text: str | None) -> int:
    """An angle expression in `pi` as the `k` of `rz(k*pi/4)`, modulo 8."""
    if not text or not re.fullmatch(r"[\d\s.+\-*/()pie]*", text):
        sys.exit(f"cannot read the angle `{text}`")
    try:
        value = eval(text.replace("pi", "math.pi"), {"__builtins__": {}, "math": math})  # noqa: S307
    except (SyntaxError, NameError, TypeError, ZeroDivisionError):
        sys.exit(f"cannot read the angle `{text}`")
    k = value / (math.pi / 4)
    if abs(k - round(k)) > 1e-9:
        sys.exit(f"`{text}` is not a multiple of pi/4: not a Clifford+T gate")
    return int(round(k)) % 8


def from_qasm(text: str) -> tuple[int, list[str]]:
    """The qubit count and gate strings of an OpenQASM 2 program on one register, or exit
    with the first statement that has no exact reading."""
    text = re.sub(r"//[^\n]*", "", text)
    n, gates = 0, []
    for stmt in (s.strip() for s in text.split(";")):
        if not stmt or stmt.startswith(("OPENQASM", "include", "creg", "barrier")):
            continue
        if stmt.startswith("qreg"):
            if n:
                sys.exit("more than one quantum register: flatten it first")
            size = re.search(r"\[(\d+)\]", stmt)
            if size is None:
                sys.exit(f"cannot read the register size in `{stmt}`")
            n = int(size[1])
            continue
        m = re.match(r"(\w+)\s*(?:\(([^)]*)\))?\s*(.*)", stmt, re.S)
        wires = [int(x) for x in re.findall(r"\[(\d+)\]", m[3])] if m else []
        if m is None or len(wires) < (2 if m[1] in ("cx", "cz") else 1):
            sys.exit(f"unsupported statement: `{stmt}` (a gate on indexed qubits was expected)")
        if len(wires) > 1 and wires[0] == wires[1]:
            sys.exit(f"`{stmt}`: a two-qubit gate on one wire is not a gate")
        name, arg = m[1], m[2]
        if name == "cx":
            gates.append(f"CX {wires[0]} {wires[1]}")
        elif name == "cz":
            gates += [f"H {wires[1]}", f"CX {wires[0]} {wires[1]}", f"H {wires[1]}"]
        elif name in ("rz", "u1", "p"):
            gates += [f"{g} {wires[0]}" for g in PHASES[eighth_turns(arg)]]
        elif name == "id":
            continue
        elif name in FROM_QASM:
            gates.append(f"{FROM_QASM[name]} {wires[0]}")
        else:
            sys.exit(f"unsupported statement: `{stmt}`")
    return n, gates


def lean_list(gates: list[str], width: int = 96) -> str:
    """The gate strings as a Lean list literal, wrapped at `width` columns."""
    lines, cur = [], "["
    for k, g in enumerate(gates):
        piece = g + ("]" if k == len(gates) - 1 else ",")
        if len(cur) + 1 + len(piece) > width and cur.strip() not in ("[", ""):
            lines.append(cur)
            cur = "    " + piece
        else:
            cur += ("" if cur in ("[", "    ") else " ") + piece
    return "\n".join(lines + [cur]) if gates else "[]"


def main() -> None:
    """`to-qasm LEAN_FILE NAME`, `to-lean QASM_FILE [--strings]`, `count QASM_FILE`."""
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("to-qasm")
    p.add_argument("lean_file", type=Path)
    p.add_argument("name", help="the name of the `def`, e.g. original")
    p = sub.add_parser("to-lean")
    p.add_argument("qasm_file", type=Path)
    p.add_argument("--strings", action="store_true",
                   help="one gate per line instead of a Lean list")
    p = sub.add_parser("count")
    p.add_argument("qasm_file", type=Path)
    args = parser.parse_args()
    if args.command == "to-qasm":
        sys.stdout.write(to_qasm(*read_lean_def(args.lean_file, args.name)))
        return
    n, gates = from_qasm(args.qasm_file.read_text())
    if args.command == "count":
        t = sum(g.split()[0] in ("T", "Tdg") for g in gates)
        cx = sum(g.startswith("CX") for g in gates)
        print(f"{n} qubits, {len(gates)} gates, T-count {t}, CNOT count {cx}")
    elif args.strings:
        print("\n".join(gates))
    else:
        print(f"-- {n} qubits, {len(gates)} gates\n{lean_list(gates)}")


if __name__ == "__main__":
    main()
