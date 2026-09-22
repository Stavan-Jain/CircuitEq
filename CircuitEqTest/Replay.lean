/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tactic

/-! # Bounded replay and cached-window regression tests -/

namespace Quantum.Circuit.ReplayTest

open Instr

set_option circuit.replayChunkSize 1

/-- Chunks include swaps and long moves on both sides of a window. -/
example : ([T 0, CX 0 1, H 3, T 0, X 2, H 4] : Circuit 5) ≡ᵤ
    [H 4, X 2, CX 0 1, S 0, H 3] := by
  circuit_windows [([T 0, T 0], [S 0])]

/-- Cancellation on the right emits inverse insertion steps. -/
example : ([H 2, X 1, T 0, Tdg 0] : Circuit 3) ≡ᵤ
    [X 1, H 0, H 2, H 0] := by
  circuit_simp

/-- Three cached windows share a row; the empty window uses the zero-wire row. -/
example : ([T 0, H 2, T 0, T 1, T 1, H 3, H 3] : Circuit 4) ≡ᵤ
    [S 1, S 0, H 2] := by
  circuit_windows [([], []), ([T 0, T 0], [S 0]),
    ([T 1, T 1], [S 1]), ([H 3, H 3], [])]

/-- A Hadamard window uses the chunked basis fallback. -/
example : ([H 0, X 0, H 0, T 1, T 1] : Circuit 2) ≡ᵤ [S 1, Z 0] := by
  circuit_windows [([H 0, X 0, H 0], [Z 0]), ([T 1, T 1], [S 1])]

/-- The proved checker accepts only its own ordered pair. -/
private def hh : Checker 1 := Checker.ofProof [H 0, H 0] [] (by circuit_simp)

/-- Caching a proof never licenses an unrelated window or a wrong placement. -/
example : hh.check [X 0] [] = false ∧ hh.check [] [H 0, H 0] = false ∧
    replay (defaultCheckers.cache ([H 0, H 0] : Circuit 1) [] (by circuit_simp))
      [Step.window 0 [0] [H 0, H 0] [] 0] ([X 0, X 0] : Circuit 1) = none := by
  decide +kernel

/-- Out-of-range cache indices are still rejected by the interpreter. -/
example : replay (fun _ => []) [.swap 3] ([H 0] : Circuit 1) = none ∧
    replay (fun _ => []) [.window 0 [0] [H 0] [H 0] 0] ([H 0] : Circuit 1) = none := by
  decide +kernel

/-- Chunking must not turn a false window into a proof. -/
example : True := by
  fail_if_success
    have : ([T 0, H 1, T 0] : Circuit 2) ≡ᵤ [Z 0, H 1] := by
      circuit_windows [([T 0, T 0], [Z 0])]
  trivial

set_option circuit.replayChunkSize 0 in
/-- Disabling chunking retains the original closing form. -/
example : ([T 0, H 1, T 0] : Circuit 2) ≡ᵤ [S 0, H 1] := by
  circuit_windows [([T 0, T 0], [S 0])]

/-- Phase goals retain their existing replay and phase validation. -/
example : ([Z 0, X 0, H 1] : Circuit 2) ≡ₚ[4] [H 1, X 0, Z 0] := by
  circuit_windows [([Z 0, X 0], [X 0, Z 0])]

end Quantum.Circuit.ReplayTest
