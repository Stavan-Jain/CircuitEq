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

Concrete circuit identities, established four ways:

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
   hand, replayed and checked by the kernel once (`CircuitEq.Certificate`).

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
under 2 GB and being killed at 7 GB (`scripts/chunked_decide.py`, which
emits such files, with `set_option Elab.async false` so that the memory of
one declaration is returned before the next starts). -/

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

end Quantum.Circuit.Examples
