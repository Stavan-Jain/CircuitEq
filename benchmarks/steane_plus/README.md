# Steane logical plus-state encoder

The seven-qubit Steane `|+_L>` encoder provides a larger original-versus-PyZX
example with an actual gate-count reduction.

## Inputs and provenance

- `original.qasm` is copied verbatim from
  [QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits/blob/3d96b5fe14a393f8eeefe02f45e5d23916b85a4d/qec_circuits/steane_713_encode_plusL.qasm).
- `pyzx.qasm` is actual PyZX **0.9.0** output from `full_reduce`,
  `extract_circuit(...).to_basic_gates()`, and `basic_optimization`.

| | Original | PyZX |
|---|---:|---:|
| Qubits | 7 | 7 |
| Hadamards | 10 | 4 |
| CNOTs | 9 | 9 |
| Total gates | 19 | 13 |

PyZX removes six Hadamards (a 31.6% total gate reduction) and reverses all
nine CNOT directions while changing their order.

## Proof

`CircuitEq/Benchmarks/SteanePlus.lean` proves exact equivalence on **every
input vector**, not just equality of the prepared state on the zero input.
The proof is a three-step `calc`:

```lean
theorem original_equiv_optimized : original ≡ᵤ optimized :=
  calc original
      = layer .H [0, 1, 3] ++ cnotNetwork edges ++ hLayer 7 := rfl
    _ ≡ᵤ _ := layer_cnotNetwork_hLayer [0, 1, 3] (by decide) edges (by decide)
    _ ≡ᵤ optimized := by circuit_simp
```

1. Read the original as a seed layer of Hadamards on qubits 0, 1, 3, the
   nine-CNOT network `edges`, and a Hadamard on every qubit. This is `rfl`.
2. Apply `layer_cnotNetwork_hLayer` (`CircuitEq/Layers.lean`), which holds
   for every register size: the final layer moves to the front, reversing
   every CNOT on the way, and cancels against the seed, leaving Hadamards
   on the complementary wires 2, 4, 5, 6. Its two side conditions, that the
   seed has no duplicates and no CNOT is degenerate, are decided.
3. `circuit_simp` (`CircuitEq/Tactic.lean`) aligns the result with PyZX's
   gate order, pulling each gate through the gates on other wires it must
   pass, each move certified by a decided commutation check.

No step enumerates the seven-qubit basis; the block theorem is proved by
induction over the network from the two-wire fact that Hadamards on both
wires of a CNOT reverse it.

## Reproduce

From the repository root, with PyZX 0.9.0 installed:

```bash
python scripts/check_pyzx_benchmarks.py steane_plus
lake build
lake env lean scripts/AxiomCheck.lean
```

Omit the Python script's argument to reproduce both benchmark fixtures. It
reruns PyZX, compares the generated QASM with the saved output, and checks
the Lean qubit counts and ordered instruction lists against both QASM files.
The QASM parser and optimizer are not formally verified; Lean independently
checks the resulting circuit pair under the existing semantics.

The new module is imported by `CircuitEq.lean` and covered by the normal
build and axiom audit. No additional axioms or `native_decide` are used.

A direct `lake env lean CircuitEq/Benchmarks/SteanePlus.lean` check took
1.9 seconds wall time locally with cached dependencies, including imports.
This is not isolated kernel time or a benchmark of the general equivalence
decision procedure.
