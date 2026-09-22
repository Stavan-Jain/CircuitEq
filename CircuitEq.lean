import CircuitEq.Zeta8
import CircuitEq.Bits
import CircuitEq.Gates
import CircuitEq.Dyadic
import CircuitEq.Chunk
import CircuitEq.Semantics
import CircuitEq.Relations
import CircuitEq.Decide
import CircuitEq.Checker
import CircuitEq.Structural
import CircuitEq.Support
import CircuitEq.PhasePoly
import CircuitEq.Tableau
import CircuitEq.Rewriting
import CircuitEq.Layers
import CircuitEq.Certificate
import CircuitEq.Defaults
import CircuitEq.Tactic
import CircuitEq.Embedding
import CircuitEq.Benchmarks.Rep3PhaseFlip
import CircuitEq.Benchmarks.SteanePlus
import CircuitEq.Benchmarks.Tof3
import CircuitEq.Benchmarks.RM15Zero
import CircuitEq.Benchmarks.BarencoTof3

/-!
# CircuitEq

Unitary equivalence of Clifford+T quantum circuits in Lean 4: a computable
coefficient field, sparse state-vector gate semantics, a decidable equivalence
relation for concrete circuits (exact, and up to a global phase that may be
left open or named), a structural toolkit for proofs that are
parametric in the qubit count (fusion and commutation, rewriting in context,
Hadamard-layer and CNOT-network algebra, the certificate language with its
replay interpreter, the `circuit_simp` and `circuit_windows` tactics, and the
locality theorem for placing circuits on selected wires), and benchmark
proofs against PyZX output. This is the umbrella module; see the README.
-/
