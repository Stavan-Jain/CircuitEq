# `[[15,1,3]]` Reed–Muller logical zero encoder

The first pair decided by the Clifford tableau checker: fifteen qubits, a
CNOT network that PyZX re-synthesises rather than reorders, and no window
or block structure to align. The tableau does not need any.

## Inputs and provenance

- `original.qasm` is copied verbatim from
  [QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits/blob/3d96b5fe14a393f8eeefe02f45e5d23916b85a4d/qec_circuits/rm15_1531_encode_0L.qasm):
  Hadamards on the four X-stabilizer seeds 0, 1, 3, 7 and a CNOT spread.
- `pyzx.qasm` is actual PyZX **0.9.0** output from `full_reduce`,
  `extract_circuit(...).to_basic_gates()`, and `basic_optimization`.

| | Original | PyZX |
|---|---:|---:|
| Qubits | 15 | 15 |
| Hadamards | 4 | 4 |
| CNOTs | 28 | 24 |
| Total gates | 32 | 28 |

PyZX removes four CNOTs (a 12.5% total gate reduction) and rewires the
network: the output contains CNOTs between former seeds (`CX 0 1`,
`CX 3 7`, each twice) that the original never has, so the two CNOT
networks are not related by commutation and cancellation alone.

## Proof

`CircuitEq/Benchmarks/RM15Zero.lean` proves `original ≡ₛ optimized`,
equality of the two unitaries up to a global unit scalar on **every input
vector**, in one line:

```lean
theorem original_equiv_optimized : original ≡ₛ optimized :=
  (tableauChecker 15).sound _ _ (by decide +kernel)
```

`tableauChecker` (`CircuitEq/Tableau.lean`) conjugates each of the 30
Pauli generators `X_j`, `Z_j` through each circuit with the standard
tableau update rules (a few `Nat` bit operations per gate and generator)
and compares the two lists of images; the kernel evaluates this in about
0.3 s. Its soundness theorem, that equal tableaux force the unitaries to
agree up to a scalar, is proved once for every qubit count from the
pointwise soundness of each update rule and the fact that an operator
commuting with every `X_j` and `Z_j` is a scalar. The relation is `≡ₛ`
rather than `≡ᵤ` because a tableau never sees the global phase.

## Reproduce

From the repository root, with PyZX 0.9.0 installed:

```bash
python scripts/check_pyzx_benchmarks.py rm15_zero
lake build
lake env lean scripts/AxiomCheck.lean
```

The Python script reruns PyZX, compares the generated QASM with the saved
output, and checks the Lean qubit counts and ordered instruction lists
against both QASM files. The QASM parser and optimizer are not formally
verified; Lean independently checks the resulting circuit pair.

The module is imported by `CircuitEq.lean` and covered by the normal build
and axiom audit. No additional axioms or `native_decide` are used.

A direct `lake env lean CircuitEq/Benchmarks/RM15Zero.lean` check used
about 1.7 s of CPU time locally with cached dependencies, including
imports (wall time ranged from 2 s to 20 s depending on machine load); the
kernel's own type checking of the theorem is 0.3–0.4 s.
