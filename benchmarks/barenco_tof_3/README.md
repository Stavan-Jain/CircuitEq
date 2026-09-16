# `barenco_tof_3`: T-count reduction by phase teleportation, six one-wire windows

The second T-heavy pair, and the first whose alignment was produced by a
script rather than by hand: `scripts/tcount_survey.py` (see
`benchmarks/survey/README.md`) diffed the two gate lists, ordered the
windows, and `circuit_windows` checked them.

## Inputs and provenance

- `original.qasm` is `barenco_tof_3` as built here: a triply-controlled NOT
  on qubits 0, 1, 2 → 4 through the dirty ancilla 3 in the Barenco et al.
  (1995) Lemma 7.2 pattern `CCX 2 3 4; CCX 0 1 3; CCX 2 3 4; CCX 0 1 3`,
  each Toffoli in the textbook seven-`T` decomposition of
  `benchmarks/tof_3/README.md`, so 5 qubits, 60 gates, T-count 28. The
  Nam–Ross–Su–Childs–Maslov benchmark of the same name has this structure
  (5 qubits, T-count 28); the gate order inside each Toffoli may differ
  from their file. The ancilla is restored whatever its initial value, so
  the circuit is `tof_3` without the clean-ancilla assumption, at the price
  of one more Toffoli.
- `pyzx.qasm` is actual PyZX **0.9.0** output from `teleport_reduce`,
  `Circuit.from_graph(...).to_basic_gates()`, then `basic_optimization`
  (the `teleport` pipeline of `scripts/check_pyzx_benchmarks.py`).

| | Original | PyZX |
|---|---:|---:|
| Qubits | 5 | 5 |
| Gates (PyZX alphabet) | 60 | 56 |
| T-count | 28 | 24 |
| Instructions in Lean | 60 | 62 |

The T-count drops by four: qubits 0 and 2 are only ever CNOT controls, so
the two `T` gates on each commute to the front and merge into one `S`.
PyZX also moves the other phases forward through CNOT controls, rewrites
three `H; CX` pairs as `CZ; H`, and cancels the two Hadamards on qubit 4
between the first and the third Toffoli (the second Toffoli does not touch
qubit 4).

## Alphabet

As for `tof_3`: `cz c t` is read as `H t; CX c t; H t` (hence 62 Lean
instructions for 56 PyZX gates) and `rz(k·π/4)` as the diagonal gate
`diag(1, e^{ikπ/4})`. The equivalence proved is exact, not up to phase.

## Proof

`CircuitEq/Benchmarks/BarencoTof3.lean` proves exact equivalence on every
input vector with one tactic call and six windows:

```lean
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_windows
    [([T 0, T 0], [S 0]),
      ([T 2, T 2], [S 2]),
      ([], [H 4, H 4]),
      ([H 4, H 4], []),
      ([], [H 3, H 3]),
      ([], [H 3, H 3])]
```

- Windows 1 and 2 are the `T · T = S` merges, decided on one qubit each.
- Windows 3, 5 and 6 are the `H; H` pairs that the three `CZ; H` rewrites
  insert (`H; CX = H; CX; H; H`), decided on one qubit each.
- Window 4 is the cancelled Hadamard pair on qubit 4.

Everything else is a checked commutation: phase gates through CNOT
controls and gates on disjoint wires. The kernel never evaluates more than
one qubit, so the whole proof is alignment work; there is no three-qubit
window like `tof_3`'s fourth, because here PyZX did not move a `CZ` through
a CNOT.

The alignment is the output of `scripts/tcount_survey.py`: a diff of the
two gate lists in a canonical order (a priority topological sort under the
tactic's own commutation relation), each opcode turned into a window,
windows ordered by replaying the tactic's rules in Python. No refinement
step was needed for this pair.

## Reproduce

From the repository root, with PyZX 0.9.0 installed:

```bash
python scripts/check_pyzx_benchmarks.py barenco_tof_3
lake build
lake env lean scripts/AxiomCheck.lean
```

The script reruns the pipeline, compares the generated QASM with the saved
output, and checks the Lean qubit count and ordered instruction lists
against both QASM files under the translation above. The QASM parser and
optimizer are not formally verified; Lean independently checks the
resulting circuit pair under the existing semantics.

The module is imported by `CircuitEq.lean` and covered by the normal build
and axiom audit. No additional axioms or `native_decide` are used.

A direct `lake env lean CircuitEq/Benchmarks/BarencoTof3.lean` check took
2.3 seconds wall time with cached dependencies on a machine shared
with four other Lean builds; the one-qubit windows are negligible and the
time is the import plus the alignment of 60 and 62 instructions.
