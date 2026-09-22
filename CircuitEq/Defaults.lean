/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Certificate
import CircuitEq.PhasePoly

/-!
# The default checker tables

The tables `circuit_simp` and `circuit_windows` replay their certificates
under. `CircuitEq.Certificate` is generic in the table and imports no
checker; this file is where a checker joins the tactics. A new certified
checker is added here, at a new index, and nothing in the certificate
language changes.
-/

namespace Quantum.Circuit

/-- The default checker table. Index `0` tries the phase-polynomial
checker first (linear in the window's gates, for CNOT-plus-diagonal
windows of any width) and falls back to the basis evaluator (cost `2 ^ k`
for a window on `k` wires); `||` is lazy in the kernel, so the evaluator
runs only when the symbolic check declines. Index `1` is syntactic
equality. The tableau checker certifies `≡ₛ`, not `≡ᵤ`, and needs a
scalar variant of `replay` before it can join a table. -/
def defaultCheckers : CheckerTable := fun k =>
  [(phasePolyChecker k).orElse (evalChecker k), syntacticChecker k]

/-- The default phase table, index for index the phase form of
`defaultCheckers`. Index `0` tries the phase-polynomial checker first, which
answers only for windows that are exactly equal (phase `0`), and falls back
to the basis evaluator with the phase named (`evalPhaseFinder`, cost `2 ^ k`
for a window on `k` wires), which is where a window that holds only up to
phase is decided. Index `1` is syntactic equality. The tableau checker
certifies `≡ₛ` and does not name a phase, so it cannot join this table. -/
def defaultPhaseFinders : PhaseTable := fun k =>
  [(phasePolyChecker k).toFinder.orElse (evalPhaseFinder k), (syntacticChecker k).toFinder]

end Quantum.Circuit
