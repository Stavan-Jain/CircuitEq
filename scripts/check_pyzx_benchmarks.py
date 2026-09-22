"""Reproduce the PyZX fixtures and check their Lean instruction lists.

Requires pyzx==0.9.0. These are transcription checks; Lean proves equivalence.

Each benchmark names its Lean module and its PyZX pipeline: ``full_reduce``
is ``full_reduce`` + ``extract_circuit`` + ``basic_optimization`` (a
re-synthesis), ``teleport`` is ``teleport_reduce`` + ``basic_optimization``
(phase teleportation, which keeps the gate skeleton). The translation to the
Lean alphabet expands ``cz c t`` to ``H t; CX c t; H t`` and ``rz(k*pi/4)``,
which PyZX reads and writes as ``diag(1, exp(i*k*pi/4))`` with no global
phase, to the diagonal Clifford+T gates with that matrix.
"""

import argparse
from pathlib import Path
import re
import sys

import pyzx as zx
from pyzx.circuit.gates import CNOT, CZ, HAD, NOT, ZPhase


BENCHMARKS = {
    "rep3_phaseflip": ("Rep3PhaseFlip", "full_reduce"),
    "steane_plus": ("SteanePlus", "full_reduce"),
    "tof_3": ("Tof3", "teleport"),
    "rm15_zero": ("RM15Zero", "full_reduce"),
    "barenco_tof_3": ("BarencoTof3", "teleport"),
}

sys.path.insert(0, str(Path(__file__).resolve().parent))
from alphabet import PHASES  # noqa: E402  (`diag(1, ω^k)` as gates, PyZX's `rz` convention)


def optimize(original: zx.Circuit, pipeline: str) -> zx.Circuit:
    """Run the named PyZX pipeline on a circuit."""
    graph = original.to_graph()
    if pipeline == "full_reduce":
        zx.simplify.full_reduce(graph)
        optimized = zx.extract_circuit(graph).to_basic_gates()
    elif pipeline == "teleport":
        zx.simplify.teleport_reduce(graph)
        optimized = zx.Circuit.from_graph(graph).to_basic_gates()
    else:
        raise ValueError(pipeline)
    return zx.optimize.basic_optimization(optimized)


def lean_instructions(circuit: zx.Circuit) -> list[str]:
    """Translate PyZX gates to the Lean alphabet, rejecting other gates."""
    instructions = []
    for gate in circuit.gates:
        if isinstance(gate, ZPhase):
            quarter_turns = gate.phase * 4
            if quarter_turns.denominator != 1:
                raise ValueError(f"Non-Clifford+T phase: {gate!r}")
            instructions += [f"{name} {gate.target}" for name in PHASES[int(quarter_turns) % 8]]
        elif isinstance(gate, HAD):
            instructions.append(f"H {gate.target}")
        elif isinstance(gate, NOT):
            instructions.append(f"X {gate.target}")
        elif isinstance(gate, CNOT):
            instructions.append(f"CX {gate.control} {gate.target}")
        elif isinstance(gate, CZ):
            instructions += [f"H {gate.target}", f"CX {gate.control} {gate.target}",
                             f"H {gate.target}"]
        else:
            raise ValueError(f"Unsupported fixture gate: {gate!r}")
    return instructions


def check_benchmark(name: str) -> None:
    """Rerun PyZX and compare both circuits with their Lean definitions."""
    if zx.__version__ != "0.9.0":
        raise RuntimeError(f"Expected PyZX 0.9.0, found {zx.__version__}")
    module, pipeline = BENCHMARKS[name]
    root = Path(__file__).resolve().parents[1]
    fixtures = root / "benchmarks" / name
    original = zx.Circuit.load(str(fixtures / "original.qasm"))
    optimized = optimize(original, pipeline)
    if optimized.to_qasm() != (fixtures / "pyzx.qasm").read_text():
        raise RuntimeError(f"{name}: PyZX output differs from the QASM fixture")

    proof = (root / "CircuitEq" / "Benchmarks" / f"{module}.lean").read_text()
    for definition, circuit in [("original", original), ("optimized", optimized)]:
        match = re.search(
            rf"def {definition} : Circuit (\d+) :=\s*\[([^\]]*)\]", proof
        )
        if match is None:
            raise RuntimeError(f"{name}: Lean definition missing: {definition}")
        instructions = [" ".join(gate.split()) for gate in match[2].split(",")]
        if int(match[1]) != circuit.qubits or instructions != lean_instructions(circuit):
            raise RuntimeError(f"{name}: Lean definition differs from QASM: {definition}")
    print(f"{name}: PyZX {zx.__version__} {pipeline}, {original.qubits} qubits, "
          f"{len(original.gates)} -> {len(optimized.gates)} gates, "
          f"T-count {original.tcount()} -> {optimized.tcount()}; "
          "output reproduced and Lean instruction lists match.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("benchmark", nargs="?", choices=BENCHMARKS)
    args = parser.parse_args()
    for name in [args.benchmark] if args.benchmark else BENCHMARKS:
        check_benchmark(name)


if __name__ == "__main__":
    main()
