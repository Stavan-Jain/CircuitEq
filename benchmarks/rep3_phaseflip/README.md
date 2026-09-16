# Three-qubit phase-flip repetition encoder

The first original-versus-PyZX equivalence proof, and the smallest: PyZX
only reorders gates, so `circuit_simp` closes the pair in one line.

## Inputs and provenance

- `original.qasm` is copied verbatim from
  [QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits/blob/3d96b5fe14a393f8eeefe02f45e5d23916b85a4d/qec_circuits/rep3_phaseflip_encode.qasm).
- `pyzx.qasm` is actual PyZX **0.9.0** output, produced by `full_reduce`,
  `extract_circuit(...).to_basic_gates()`, then `basic_optimization`.
- Both circuits have **3 qubits and 5 gates**. This example exercises a
  changed gate order; it does not demonstrate a gate-count reduction.

```text
Original: CX 0 1; CX 0 2; H 0; H 1; H 2
PyZX:     CX 0 1; H 1; CX 0 2; H 2; H 0
```

## Proof and checks

`CircuitEq/Benchmarks/Rep3PhaseFlip.lean` contains:

- `original_equiv_optimized`: equality on **every input vector**, with no
  global-phase correction, proved by `circuit_simp`. The tactic pulls each
  gate of the PyZX order through the gates on other wires it must pass;
  every move is a decided commutation check.
- `reorder`: the same fact for any three distinct qubits in any register,
  from the commutation lemmas directly.

The module is imported by `CircuitEq.lean`, so normal builds and the CI axiom
audit include these declarations. No new evaluator, axioms, or
`native_decide` are used.

## Reproduce

From the repository root, with Python and PyZX 0.9.0 installed:

```bash
python scripts/check_pyzx_benchmarks.py rep3_phaseflip
lake build
lake env lean scripts/AxiomCheck.lean
```

The Python script reruns PyZX, compares its output with the stored QASM, and
checks that both Lean instruction lists match the parsed QASM. It does not
formally verify the QASM parser or optimizer; the Lean theorem checks the
resulting circuit pair independently.

A direct `lake env lean CircuitEq/Benchmarks/Rep3PhaseFlip.lean` check took
1.6 seconds wall time locally with cached dependencies, including imports.
This is a local end-to-end measurement, not isolated kernel time or evidence
of scaling to larger circuits.
