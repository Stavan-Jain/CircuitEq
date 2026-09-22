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
import CircuitEq.Lanes
import CircuitEq.PhasePoly
import CircuitEq.PhasePoly.Complete
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
import CircuitEq.Benchmarks.Cuccaro4

/-!
# CircuitEq

Unitary equivalence of Clifford+T quantum circuits in Lean 4. The trusted
core is `CircuitEq.Semantics`: circuits, their state-vector denotation over
the computable field `ℚ(ζ₈)` (`CircuitEq.Zeta8`), and the relations `≡ᵤ`,
`≡ₚ[k]`, `≡ₚ` and `≡ₛ`. Around it: their algebra (`Relations`), decision
by kernel evaluation on the gcd-free ring `ℤ[ω, 1/√2]` (`Dyadic`, `Decide`,
chunked by `Chunk`), the checker contract (`Checker`) and two certified
fragment checkers, the phase-polynomial normal form for CNOT plus diagonal
gates (`Lanes`, `PhasePoly`, `PhasePoly.Complete`) and the Clifford tableau
(`Tableau`), a toolkit for proofs parametric in the qubit count
(`Structural`, `Support`, `Rewriting`, `Layers`, and the locality theorem in
`Embedding`), the certificate language with its replay interpreter
(`Certificate`, `Defaults`), the `circuit_simp` and `circuit_windows`
tactics that emit it (`Tactic`), and benchmark proofs against PyZX output.
This is the umbrella of the library; `CircuitEqTest.lean` is that of the
examples and tests. See the README.
-/
