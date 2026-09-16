# `tof_3`: T-count reduction by phase teleportation

The first T-heavy pair: the standard `tof_3` circuit against PyZX's
structure-preserving T-count optimisation of it. This is the pair that
exercises `circuit_windows`.

## Inputs and provenance

- `original.qasm` is `tof_3` as built here: a doubly-controlled NOT on
  qubits 0, 1 → 4 computed through the clean ancilla 3 as three Toffolis
  `CCX 0 1 3; CCX 3 2 4; CCX 0 1 3`, each in the textbook seven-`T`
  decomposition

  ```text
  CCX a b c = H c; CX b c; T† c; CX a c; T c; CX b c; T† c; CX a c;
              T b; T c; H c; CX a b; T a; T† b; CX a b
  ```

  so 5 qubits, 45 gates, T-count 21. The Nam–Ross–Su–Childs–Maslov
  benchmark of the same name has this structure; the gate order inside each
  Toffoli may differ from their file.
- `pyzx.qasm` is actual PyZX **0.9.0** output from `teleport_reduce`,
  `Circuit.from_graph(...).to_basic_gates()`, then `basic_optimization`.
  Phase teleportation keeps the gate skeleton and only moves and merges
  phases, which is what makes the pair alignable window by window. Full
  re-synthesis (`full_reduce` + extraction) reaches T-count 15 on this
  input but produces a structurally unrelated 49-gate circuit; the window
  pattern does not apply to it.

| | Original | PyZX |
|---|---:|---:|
| Qubits | 5 | 5 |
| Gates (PyZX alphabet) | 45 | 44 |
| T-count | 21 | 19 |
| Instructions in Lean | 45 | 50 |

The T-count drops by two because qubit 0 is only ever a CNOT control, so
its two `T` gates commute to the front and merge into one `S`. PyZX also
moves the other phases forward through CNOT controls and rewrites three
`H; CX` pairs as `CZ; H`.

## Alphabet

Lean has `H, X, Y, Z, S, S†, T, T†, CX`. The translation in
`scripts/check_pyzx_benchmarks.py` expands `cz c t` to `H t; CX c t; H t`,
hence 50 Lean instructions for 44 PyZX gates, and reads `rz(k·π/4)` as the
diagonal gate `diag(1, e^{ikπ/4})`. That is PyZX's own semantics for the
`rz` it writes, with no global phase; Qiskit's `rz` differs by one, see the
roadmap's Rung 2. The equivalence proved is exact, not up to phase.

## Proof

`CircuitEq/Benchmarks/Tof3.lean` proves exact equivalence on every input
vector with one tactic call and four windows:

```lean
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_windows
    [([T 0, T 0], [S 0]),
      ([H 3, CX 1 3], [H 3, CX 1 3, H 3, H 3]),
      ([H 4, CX 2 4], [H 4, CX 2 4, H 4, H 4]),
      ([Tdg 2, CX 3 2, H 3, CX 1 3], [H 3, CX 1 3, H 3, Tdg 2, CX 3 2, H 3])]
```

- Window 1 is the `T · T = S` merge, decided on one qubit.
- Windows 2 and 3 are `H; CX = CZ; H`, decided on two qubits.
- Window 4 is the `CZ` that PyZX commuted through a CNOT on its control,
  which as `H; CX; H` is not a gate-by-gate commutation; decided on three
  qubits.

Everything else is a checked commutation: a phase gate through the control
of a CNOT (`T 0` past `CX 0 3` and `CX 0 1`, `T 1` past `CX 1 3`, and so
on), gates on disjoint wires, and diagonal gates past each other. The rule
for a diagonal gate on a CNOT control was added to `Instr.CanCommute` for
this pair. The kernel never evaluates more than three qubits.

The alignment was written by hand from the diff of the two gate lists. The
tactic's error messages, which name the blocked gate and the pending
window, are the intended feedback loop for an agent doing the same.

## Reproduce

From the repository root, with PyZX 0.9.0 installed:

```bash
python scripts/check_pyzx_benchmarks.py tof_3
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

A direct `lake env lean CircuitEq/Benchmarks/Tof3.lean` check takes about
5 seconds wall time with cached dependencies. About 3 of them are the kernel
deciding the three-qubit window, and the alignment itself is well under a
second. Before the materialised evaluator (`evalList` in `Semantics.lean`)
the same file took 12 seconds; the difference is that window's `2^depth`
re-reads of the input under the closure-based `denote`.
