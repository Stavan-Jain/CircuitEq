import CircuitEq.Zeta8
import CircuitEq.Bits
import CircuitEq.Gates
import CircuitEq.Semantics
import CircuitEq.Structural
import CircuitEq.Rewriting
import CircuitEq.Layers
import CircuitEq.Tactic
import CircuitEq.Embedding
import CircuitEq.Examples
import CircuitEq.Benchmarks.Rep3PhaseFlip
import CircuitEq.Benchmarks.SteanePlus
import CircuitEq.Benchmarks.Tof3

/-!
# CircuitEq

Unitary equivalence of Clifford+T quantum circuits in Lean 4: a computable
coefficient field, sparse state-vector gate semantics, a decidable equivalence
relation for concrete circuits, a structural toolkit for proofs that are
parametric in the qubit count (fusion and commutation, rewriting in context,
Hadamard-layer and CNOT-network algebra, the `circuit_simp` tactic, and the
locality theorem for placing circuits on selected wires), and benchmark
proofs against PyZX output. This is the umbrella module; see the README.
-/
