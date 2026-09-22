/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Structural
import CircuitEq.Embedding
import CircuitEq.Tactic

/-!
# Worked equivalences

Concrete circuit identities, established six ways:

1. **decided** — the kernel checks the `2 ^ n` computational-basis vectors
   (`decide +kernel`, via `decidableEquivalent`), in one declaration or in
   chunks (`CircuitEq.Chunk`);
2. **disproved** — the same decision procedure refutes a false equivalence,
   and separates "equal" from "equal up to a global phase";
3. **structural** — parametric in the qubit count `n` and the qubit indices,
   assembled from the toolkit in `CircuitEq.Structural` with `2 × 2`
   matrix leaves;
4. **placed** — a decided identity on `k` qubits, lifted to any `k` distinct
   wires of any register by `Equivalent.rename` (`CircuitEq.Embedding`);
5. **certified** — a list of rewrite steps, found by a tactic or written by
   hand, replayed and checked by the kernel once (`CircuitEq.Certificate`);
6. **up to a global phase** — all of the above for `≡ₚ`, and for `≡ₚ[k]`
   with the exponent of `ω` named: decided, chained in `calc`, placed, and
   certified with windows that hold only up to a phase.

The structural and placed proofs are the point of the prototype: they hold
for every `n` and every choice of qubits, which no fixed-size equivalence
checker can even state.
-/

namespace Quantum.Circuit.Examples

open Quantum.Circuit Instr

/-! ### Decided on the computational basis -/

/-- `T² = S`. -/
theorem T_T_eq_S : ([T 0, T 0] : Circuit 1) ≡ᵤ [S 0] := by decide +kernel

/-- `S² = Z`. -/
theorem S_S_eq_Z : ([S 0, S 0] : Circuit 1) ≡ᵤ [Z 0] := by decide +kernel

/-- `HXH = Z`. -/
theorem H_X_H_eq_Z : ([H 0, X 0, H 0] : Circuit 1) ≡ᵤ [Z 0] := by decide +kernel

/-- `HZH = X`. -/
theorem H_Z_H_eq_X : ([H 0, Z 0, H 0] : Circuit 1) ≡ᵤ [X 0] := by decide +kernel

/-- `S X S† = Y`; as a circuit, `S†` runs first. -/
theorem Sdg_X_S_eq_Y : ([Sdg 0, X 0, S 0] : Circuit 1) ≡ᵤ [Y 0] := by decide +kernel

/-- `T⁸ = I`. -/
theorem T_pow_eight : ([T 0, T 0, T 0, T 0, T 0, T 0, T 0, T 0] : Circuit 1) ≡ᵤ [] := by
  decide +kernel

/-- CNOT is an involution. -/
theorem cnot_cnot : ([CX 0 1, CX 0 1] : Circuit 2) ≡ᵤ [] := by decide +kernel

/-- Conjugating a CNOT by `H ⊗ H` reverses control and target. -/
theorem hh_cnot_hh : ([H 0, H 1, CX 0 1, H 0, H 1] : Circuit 2) ≡ᵤ [CX 1 0] := by
  decide +kernel

/-- The two three-CNOT decompositions of SWAP agree. -/
theorem swap_swap : ([CX 0 1, CX 1 0, CX 0 1] : Circuit 2) ≡ᵤ [CX 1 0, CX 0 1, CX 1 0] := by
  decide +kernel

/-- CZ is symmetric in its two qubits. -/
theorem cz_symm : ([H 1, CX 0 1, H 1] : Circuit 2) ≡ᵤ [H 0, CX 1 0, H 0] := by decide +kernel

/-- `T` on the control commutes through a CNOT (concrete instance; see
`T_cnot_comm` below for every `n`). -/
theorem T_cnot_comm₂ : ([T 0, CX 0 1] : Circuit 2) ≡ᵤ [CX 0 1, T 0] := by decide +kernel

/-- A CNOT ladder over a middle qubit implements a long-range CNOT. -/
theorem cx_ladder : ([CX 0 1, CX 1 2, CX 0 1, CX 1 2] : Circuit 3) ≡ᵤ [CX 0 2] := by
  decide +kernel

/-! ### Decided in chunks

The same decision, one declaration per range of basis vectors
(`CircuitEq.Chunk`), so the kernel's memory is that of one range. It buys
nothing at three qubits; at seven it is the difference between finishing
and running out of memory (measured in `benchmarks/scale/README.md`;
`scripts/chunked_decide.py` emits such files, with
`set_option Elab.async false` so that the memory of one declaration is
returned before the next starts). -/

/-- The ladder identity on the basis vectors `|0⟩, …, |3⟩`. -/
theorem cx_ladder_lo :
    (List.range' 0 4).all
      (checkEquivAt ([CX 0 1, CX 1 2, CX 0 1, CX 1 2] : Circuit 3) [CX 0 2]) = true := by
  decide +kernel

/-- The ladder identity on the basis vectors `|4⟩, …, |7⟩`. -/
theorem cx_ladder_hi :
    (List.range' 4 4).all
      (checkEquivAt ([CX 0 1, CX 1 2, CX 0 1, CX 1 2] : Circuit 3) [CX 0 2]) = true := by
  decide +kernel

/-- The ladder identity, assembled from its two chunks. -/
theorem cx_ladder_chunked : ([CX 0 1, CX 1 2, CX 0 1, CX 1 2] : Circuit 3) ≡ᵤ [CX 0 2] :=
  equivalent_of_allBelow (((AllBelow.zero _).add cx_ladder_lo).add cx_ladder_hi)

/-- Up to a phase, chunk by chunk: `Z X = −X Z`, with the phase `ω ^ 4 = −1`
named by the proof. -/
theorem Z_X_phase_chunk :
    (List.range' 0 2).all (checkEquivUpToPhaseAt ([Z 0, X 0] : Circuit 1) [X 0, Z 0] 4) = true := by
  decide +kernel

/-- `Z X ≡ₚ X Z`, assembled from its one chunk. -/
theorem Z_X_phase_chunked : ([Z 0, X 0] : Circuit 1) ≡ₚ [X 0, Z 0] :=
  equivalentUpToPhase_of_allBelow (by decide) ((AllBelow.zero _).add Z_X_phase_chunk)

/-! ### Disproved -/

/-- `H` and `T` do not commute. -/
theorem not_H_T_comm : ¬ (([H 0, T 0] : Circuit 1) ≡ᵤ [T 0, H 0]) := by decide +kernel

/-- `Z` and `X` anticommute, so the two orders are not equal … -/
theorem not_Z_X_comm : ¬ (([Z 0, X 0] : Circuit 1) ≡ᵤ [X 0, Z 0]) := by decide +kernel

/-- … but they are equal up to the global phase `-1 = ω⁴`. -/
theorem Z_X_phase_X_Z : ([Z 0, X 0] : Circuit 1) ≡ₚ [X 0, Z 0] := by decide +kernel

/-- The same with the phase named: `Z X = ω⁴ · X Z`, and no other power. -/
theorem Z_X_eq_neg_X_Z : ([Z 0, X 0] : Circuit 1) ≡ₚ[4] [X 0, Z 0] := by decide +kernel

/-- The named form is refutable too: the phase is not `ω³`. -/
theorem not_Z_X_phase_three : ¬ (([Z 0, X 0] : Circuit 1) ≡ₚ[3] [X 0, Z 0]) := by
  decide +kernel

/-- `T` on the *target* does not commute through a CNOT. -/
theorem not_T_target_cnot_comm : ¬ (([T 1, CX 0 1] : Circuit 2) ≡ᵤ [CX 0 1, T 1]) := by
  decide +kernel

/-! ### Structural, for every `n` -/

variable {n : ℕ}

/-- `H² = I` on any qubit of any register. -/
theorem H_H_cancel (i : Fin n) : [H i, H i] ≡ᵤ ([] : Circuit n) :=
  cancel_of_mul_eq_one Gate1.H_mul_H i

/-- `T² = S` on any qubit of any register. -/
theorem T_T_eq_S' (i : Fin n) : [T i, T i] ≡ᵤ ([S i] : Circuit n) :=
  fuse Gate1.T_mul_T i

/-- `HXH = Z` on any qubit of any register. -/
theorem H_X_H_eq_Z' (i : Fin n) : [H i, X i, H i] ≡ᵤ ([Z i] : Circuit n) :=
  fuse₃ Gate1.H_mul_X_mul_H i

/-- `T` and `H` on different qubits commute. -/
theorem T_H_comm {i j : Fin n} (h : i ≠ j) : [T i, H j] ≡ᵤ ([H j, T i] : Circuit n) :=
  one_one_comm h _ _

/-- `T` on the control commutes through a CNOT, for every `n`. The leaf fact,
that `T` is diagonal, is decided by the kernel. -/
theorem T_cnot_comm {c t : Fin n} (h : c ≠ t) : [T c, CX c t] ≡ᵤ ([CX c t, T c] : Circuit n) :=
  cnot_diag_control_comm h (by decide +kernel)

/-- A `T` between two Hadamards on a different qubit: commute, then cancel.
A three-step `calc` in the equivalence relation. -/
theorem H_T_H_eq_T {i j : Fin n} (h : i ≠ j) : [H i, T j, H i] ≡ᵤ ([T j] : Circuit n) :=
  calc ([H i, T j, H i] : Circuit n) = [H i, T j] ++ [H i] := rfl
    _ ≡ᵤ [T j, H i] ++ [H i] := (one_one_comm h _ _).append (Equivalent.refl _)
    _ = [T j] ++ [H i, H i] := rfl
    _ ≡ᵤ [T j] ++ [] := (Equivalent.refl _).append (H_H_cancel i)
    _ = [T j] := rfl

/-- A layer of Hadamards on every qubit is self-inverse, for every `n`. -/
theorem hLayer_cancel (n : ℕ) : hLayer n ++ hLayer n ≡ᵤ [] := hLayer_hLayer n

/-! ### Decided on `k` qubits, placed on any `k` wires

The kernel pays `2 ^ k` for the small identity; `Equivalent.rename` moves it
to any distinct wires of an `n`-qubit register at no further cost. -/

/-- `H ⊗ H` conjugation reverses a CNOT on any two distinct wires: the
two-qubit fact `hh_cnot_hh`, placed on `i, j`. -/
theorem hh_cnot_hh' {i j : Fin n} (h : i ≠ j) :
    [H i, H j, CX i j, H i, H j] ≡ᵤ ([CX j i] : Circuit n) := by
  simpa [wires₂] using hh_cnot_hh.rename (wires₂ h)

/-- The CNOT ladder implements a long-range CNOT over any middle wire: the
three-qubit fact `cx_ladder`, placed on `a, b, c`. -/
theorem cx_ladder' {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    [CX a b, CX b c, CX a b, CX b c] ≡ᵤ ([CX a c] : Circuit n) := by
  simpa [wires₃] using cx_ladder.rename (wires₃ hab hac hbc)

/-! ### The window pattern

An optimiser changed a circuit in two places: it fused `T · T` into `S` on
qubit 0 and deleted a Hadamard pair on qubit 5, leaving the other gates
where they were. The alignment names the two windows; `circuit_windows`
decides each on its own wires (one and one qubit here, never six), places
it back, and checks that every other gate can be moved into position. -/

/-- Two local rewrites with context gates in between. -/
theorem two_windows :
    ([T 0, CX 1 2, T 0, H 5, X 3, H 5] : Circuit 6) ≡ᵤ [CX 1 2, S 0, X 3] := by
  circuit_windows [([T 0, T 0], [S 0]), ([H 5, H 5], [])]

/-! ### The certificate

What `circuit_windows` finds is data: a list of `Step`s that `replay`
turns into the right-hand circuit. The same proof written out as that
data, closed by `circuit_replay`; each move names its position, the
windows name their wires, and the kernel checks the trace once. This is
the form an external search emits. -/

/-- `two_windows` as an explicit certificate: move the second `T 0` left
past the CNOT, fuse on wire `0`, move the CNOT back to the front, bring
the Hadamards together past `X 3`, and delete them on wire `5`. -/
theorem two_windows_certificate :
    ([T 0, CX 1 2, T 0, H 5, X 3, H 5] : Circuit 6) ≡ᵤ [CX 1 2, S 0, X 3] := by
  circuit_replay defaultCheckers
    [.moveLeft 2 1, .window 0 [0] ([T 0, T 0] : Circuit 1) [S 0] 0, .moveLeft 1 1,
      .moveLeft 4 1, .window 2 [5] ([H 0, H 0] : Circuit 1) [] 0]

/-! ### Up to a global phase

An optimiser preserves a circuit only up to a global phase, and the phase
appears inside a window: `Z X` against `X Z` is `ω⁴`. `≡ₚ` composes as `≡ᵤ`
does: in `calc`, under `append` and `in_context`, by the locality theorem,
and in the window pattern. `≡ₚ[k]` is the same relation with the exponent
of `ω` named, and the exponents add modulo eight. -/

/-- `Y = i · X Z`: as a circuit, `Y` is `Z` then `X`, up to `ω² = i`. -/
theorem Y_eq_Z_X : ([Y 0] : Circuit 1) ≡ₚ[2] [Z 0, X 0] := by decide +kernel

/-- A `calc` that mixes the relations: an exact fusion, then a step that
holds only up to a phase. One `≡ₚ` step makes the chain `≡ₚ`. -/
theorem T_T_Z_X_phase : ([T 0, T 0, Z 0, X 0] : Circuit 1) ≡ₚ [S 0, X 0, Z 0] :=
  calc ([T 0, T 0, Z 0, X 0] : Circuit 1)
      = [T 0, T 0] ++ [Z 0, X 0] := rfl
    _ ≡ᵤ [S 0] ++ [Z 0, X 0] := T_T_eq_S.append (Equivalent.refl _)
    _ ≡ₚ [S 0] ++ [X 0, Z 0] := (EquivalentUpToPhase.refl _).append Z_X_phase_X_Z
    _ = [S 0, X 0, Z 0] := rfl

/-- With the phases named, a `calc` adds them: `ω² · ω⁴ = ω⁶`, and the
statement's `6` is checked against `2 + 4` by unification. -/
theorem Y_Z_X_phase : ([Y 0, Z 0, X 0] : Circuit 1) ≡ₚ[6] [Z 0, X 0, X 0, Z 0] :=
  calc ([Y 0, Z 0, X 0] : Circuit 1)
      = [Y 0] ++ [Z 0, X 0] := rfl
    _ ≡ₚ[2] [Z 0, X 0] ++ [Z 0, X 0] := Y_eq_Z_X.append_right _
    _ ≡ₚ[4] [Z 0, X 0] ++ [X 0, Z 0] := Z_X_eq_neg_X_Z.append_left _
    _ = [Z 0, X 0, X 0, Z 0] := rfl

/-- `Z X = −X Z` on any wire of any register: the one-qubit fact, placed by
the locality theorem for phase, which keeps the phase. -/
theorem Z_X_eq_neg_X_Z' (i : Fin n) : [Z i, X i] ≡ₚ[4] ([X i, Z i] : Circuit n) := by
  simpa [wires₁] using Z_X_eq_neg_X_Z.rename (wires₁ i)

/-- The window pattern up to a global phase. The first window is an exact
fusion; the second holds only up to `ω⁴`, which the kernel finds on wire
`3` alone, and every other move is an exact commutation. -/
theorem two_windows_phase :
    ([T 0, CX 1 2, T 0, Z 3, X 3, H 5] : Circuit 6) ≡ₚ [CX 1 2, S 0, X 3, Z 3, H 5] := by
  circuit_windows [([T 0, T 0], [S 0]), ([Z 3, X 3], [X 3, Z 3])]

/-- The same proof with the phase named: the kernel adds the windows'
phases up, `0 + 4`, and compares the sum with the statement's. -/
theorem two_windows_phase_named :
    ([T 0, CX 1 2, T 0, Z 3, X 3, H 5] : Circuit 6) ≡ₚ[4] [CX 1 2, S 0, X 3, Z 3, H 5] := by
  circuit_windows [([T 0, T 0], [S 0]), ([Z 3, X 3], [X 3, Z 3])]

/-- The same as an explicit certificate, replayed up to phase: the steps
are those of an exact certificate, and only the table differs. -/
theorem two_windows_phase_certificate :
    ([T 0, CX 1 2, T 0, Z 3, X 3, H 5] : Circuit 6) ≡ₚ[4] [CX 1 2, S 0, X 3, Z 3, H 5] := by
  circuit_replay_phase defaultPhaseFinders
    [.moveLeft 2 1, .window 0 [0] ([T 0, T 0] : Circuit 1) [S 0] 0, .moveLeft 1 1,
      .window 2 [3] ([Z 0, X 0] : Circuit 1) [X 0, Z 0] 0]

/-- A segment of a longer circuit, proved on its own: phase `ω⁴`. -/
theorem segment_one : ([Z 0, X 0, CX 0 1] : Circuit 2) ≡ₚ[4] [X 0, Z 0, CX 0 1] := by
  circuit_windows [([Z 0, X 0], [X 0, Z 0])]

/-- The next segment, proved on its own: phase `ω²`. -/
theorem segment_two : ([Y 1, H 0] : Circuit 2) ≡ₚ[2] [Z 1, X 1, H 0] := by
  circuit_windows [([Y 1], [Z 1, X 1])]

/-- Segments compose, and their phases add: `ω⁴ · ω² = ω⁶`. Each segment is
its own declaration, so the kernel holds one segment's replay at a time;
this is how a long pair is proved without one long replay. -/
theorem segments_phase :
    ([Z 0, X 0, CX 0 1, Y 1, H 0] : Circuit 2) ≡ₚ[6] [X 0, Z 0, CX 0 1, Z 1, X 1, H 0] :=
  segment_one.append segment_two

/-- A named phase is an exact equivalence once the phase gadget is
appended: four rounds of `H S H S H S`, Clifford gates only, denote `ω⁴`.
This is how a pair that is equal only up to a phase is normalised to an
exact one at no `T`-cost. -/
theorem two_windows_phase_exact :
    ([T 0, CX 1 2, T 0, Z 3, X 3, H 5] : Circuit 6) ≡ᵤ
      [CX 1 2, S 0, X 3, Z 3, H 5] ++ phaseGadget 4 0 :=
  (equivalentWithPhase_iff_phaseGadget 4 0 _ _).1 two_windows_phase_named

end Quantum.Circuit.Examples
