/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Rewriting
import CircuitEq.Embedding
import CircuitEq.Checker
import CircuitEq.Support

/-!
# The certificate language and its replay interpreter

A *certificate* is a list of rewrite steps (`Step n`), plain data with no
proofs inside, that an agent or an external tool emits to justify
`c₁ ≡ᵤ c₂`. `replay Cs steps c₁` runs the steps on the instruction list,
checking each with a cheap syntactic test, and returns `some c₂` when every
step is licensed. `replay_sound` says the result is equivalent to the input,
so a proof is one application of that theorem to a kernel evaluation of
`replay`: the proof term is constant-size, and the kernel's work is one
check per step, never a re-check of a whole prefix per move.

## Steps

Positions are indices into the instruction list, in time order.

* `swap i` exchanges the gates at `i` and `i + 1`; licensed by
  `Instr.CanCommute`, the syntactic commutation check of
  `CircuitEq.Rewriting`, so every rule added there is a certificate step.
* `moveLeft i d` moves the gate at `i` left by `d` positions and
  `moveRight i d` moves it right by `d`; licensed when the gate's wire
  support (`Instr.support`, a bitmask) is disjoint from the support of the
  block it crosses, one `Nat.land` after a fold of `Nat.lor` over the block.
  A gate that must pass a non-disjoint but commuting gate (a phase gate
  through a CNOT control) uses `swap` for that one crossing.
* `cancel i` deletes the gates at `i` and `i + 1`; licensed by
  `Instr.CanCancel`. `insert i a b` is its inverse, inserting the
  cancelling pair `a, b`, so that one trace can also account for an inverse
  pair present only in the target.
* `window i wires a b k` replaces the gates at `i .. i + |a| - 1`, which
  must be syntactically `rename (wiresOf wires _) a`, by
  `rename (wiresOf wires _) b`; licensed when `wires` has no duplicate and
  checker number `k` of the table's row for `wires.length` qubits accepts
  `(a, b)`. The window is stated on its own wires, so the checker's cost
  depends on `wires.length`, never on `n`.

A checker table `Cs : CheckerTable` gives, for each register size, the
checkers a window may name by index. `defaultCheckers` has the basis
evaluator `evalChecker` at index `0` and `syntacticChecker` at index `1`;
every certified checker written against `CircuitEq.Checker` can be added to
a table, and `replay_sound` holds for every table because each checker
carries its own proof.

## Replay

`replay` is structural recursion over the trace; each step is one walk to
its position (`rewriteAt`) and a local rewrite of the remainder, with
`Bool` checks and the decidable checks above through their existing
instances, so the kernel evaluates it under `decide +kernel`. `none` means
a step was not licensed; nothing is ever assumed about the input. The
closing form is

```lean
theorem foo : c₁ ≡ᵤ c₂ := replay_sound defaultCheckers steps (by decide +kernel)
```

or the macro `circuit_replay defaultCheckers steps`. The tactics of
`CircuitEq.Tactic` search for a trace in meta code and close the goal this
way, so their kernel cost is that of one `replay`.

`Step` and `replay` are meant to be mirrored outside Lean, so that a search
can run the same interpreter fast and hand Lean only the data
(`scripts/certificate.py`); a step the mirror accepts and `replay` rejects
is a bug in the mirror, never a soundness problem.

## Kernel cost

A step costs one pass over the prefix before its position plus one over
the block it crosses, at roughly 20–30 µs per list cell in the kernel
(structural recursion unfolds through `brecOn`), so a trace of `s` moves on
a circuit of `m` gates costs `O(s · m)`: about 0.1 s for 50 moves on 64
gates and 0.5 s for 100 moves on 128 gates, measured. Windows cost their
checker, `2 ^ k` for the evaluator on `k` wires, and dominate real
benchmarks. The next lever for long circuits is a `Nat` encoding of the
instruction list, on which a move is a handful of GMP-accelerated
bit operations instead of a walk.
-/

namespace Quantum.Circuit

variable {n : ℕ}

/-- A checker table: for each register size `k`, the checkers a `window`
step may name by index. -/
abbrev CheckerTable := (k : ℕ) → List (Checker k)

/-- One certificate step. Positions index the instruction list; see the
module docstring for what licenses each step. -/
inductive Step (n : ℕ) where
  /-- Exchange the gates at positions `i` and `i + 1` (`Instr.CanCommute`). -/
  | swap (i : ℕ)
  /-- Move the gate at position `i` left by `d` positions, across a block
  of disjoint wire support. -/
  | moveLeft (i d : ℕ)
  /-- Move the gate at position `i` right by `d` positions, across a block
  of disjoint wire support. -/
  | moveRight (i d : ℕ)
  /-- Delete the gates at positions `i` and `i + 1` (`Instr.CanCancel`). -/
  | cancel (i : ℕ)
  /-- Insert the cancelling pair `a, b` at position `i` (`Instr.CanCancel`). -/
  | insert (i : ℕ) (a b : Instr n)
  /-- Replace `rename (wiresOf wires _) a` at position `i` by
  `rename (wiresOf wires _) b`, accepted by checker `k` of the table's row
  for `wires.length` qubits. -/
  | window (i : ℕ) (wires : List (Fin n)) (a b : Circuit wires.length) (k : ℕ)
  deriving Repr

/-! ### Walking to a position

Every step is one walk to its position followed by a local rewrite of the
remainder, so its kernel cost is one pass over the prefix plus the local
work; the prefix is rebuilt on the way back and nothing is traversed twice.
(A lazy `take`/`drop`/`++` formulation costs several passes per step and
was measured at 2.5 times this.) -/

/-- Walk `k` gates, rewrite the remainder with `f`, and rebuild the prefix;
`none` if the circuit is shorter than `k` or `f` fails. -/
def rewriteAt (f : Circuit n → Option (Circuit n)) : ℕ → Circuit n → Option (Circuit n)
  | 0, c => f c
  | _ + 1, [] => none
  | k + 1, g :: c =>
    match rewriteAt f k c with
    | some c' => some (g :: c')
    | none => none

/-- A local rewrite that preserves equivalence does so at any position. -/
lemma rewriteAt_sound {f : Circuit n → Option (Circuit n)}
    (hf : ∀ {rest rest' : Circuit n}, f rest = some rest' → rest ≡ᵤ rest') {k : ℕ}
    {c c' : Circuit n} (h : rewriteAt f k c = some c') : c ≡ᵤ c' := by
  induction k generalizing c c' with
  | zero => exact hf h
  | succ k ih =>
    cases c with
    | nil => exact absurd h (by simp [rewriteAt])
    | cons g c =>
      rw [rewriteAt] at h
      split at h
      · next c₀ hc₀ =>
        cases h
        exact (ih hc₀).cons g
      · exact absurd h (by simp)

/-! ### The local rewrites, one per step kind -/

/-- `swap`: exchange the first two gates when they pass `Instr.CanCommute`. -/
def swapFront : Circuit n → Option (Circuit n)
  | a :: b :: rest => if a.CanCommute b then some (b :: a :: rest) else none
  | _ => none

lemma swapFront_sound {c c' : Circuit n} (h : swapFront c = some c') : c ≡ᵤ c' := by
  unfold swapFront at h
  split at h
  · next a b rest =>
    split at h
    · next hab =>
      cases h
      exact hab.sound.append (Equivalent.refl rest)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `cancel`: delete the first two gates when they pass `Instr.CanCancel`. -/
def cancelFront : Circuit n → Option (Circuit n)
  | a :: b :: rest => if a.CanCancel b then some rest else none
  | _ => none

lemma cancelFront_sound {c c' : Circuit n} (h : cancelFront c = some c') : c ≡ᵤ c' := by
  unfold cancelFront at h
  split at h
  · next a b rest =>
    split at h
    · next hab =>
      cases h
      exact hab.sound.append (Equivalent.refl _)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `insert`: insert the cancelling pair `a, b` in front. -/
def insertFront (a b : Instr n) (rest : Circuit n) : Option (Circuit n) :=
  if a.CanCancel b then some (a :: b :: rest) else none

lemma insertFront_sound {a b : Instr n} {c c' : Circuit n} (h : insertFront a b c = some c') :
    c ≡ᵤ c' := by
  unfold insertFront at h
  split at h
  · next hab =>
    cases h
    exact hab.sound.symm.append (Equivalent.refl c)
  · exact absurd h (by simp)

/-- A block crossed leftwards by the gate after it: the block's support,
the gate, and the block re-appended to what followed the gate. -/
structure Crossing (n : ℕ) where
  /-- `support` of the block crossed. -/
  mask : ℕ
  /-- The gate that crosses. -/
  gate : Instr n
  /-- The block, then what followed the gate. -/
  tail : Circuit n

/-- Cross the first `k` gates: one pass that folds their support and
rebuilds them behind the gate that follows them. -/
def pullBlock : ℕ → Circuit n → Option (Crossing n)
  | 0, g :: tail => some ⟨0, g, tail⟩
  | k + 1, x :: rest =>
    match pullBlock k rest with
    | some r => some ⟨x.support ||| r.mask, r.gate, x :: r.tail⟩
    | none => none
  | _, [] => none

/-- What `pullBlock` computes, as a split of its input. -/
lemma pullBlock_spec {k : ℕ} {c : Circuit n} {r : Crossing n} (h : pullBlock k c = some r) :
    ∃ block tail, c = block ++ r.gate :: tail ∧ r.tail = block ++ tail ∧
      r.mask = support block := by
  induction k generalizing c r with
  | zero =>
    cases c with
    | nil => exact absurd h (by simp [pullBlock])
    | cons g tail =>
      rw [pullBlock] at h
      cases h
      exact ⟨[], tail, rfl, rfl, rfl⟩
  | succ k ih =>
    cases c with
    | nil => exact absurd h (by simp [pullBlock])
    | cons x rest =>
      rw [pullBlock] at h
      split at h
      · next r₀ hr₀ =>
        cases h
        obtain ⟨block, tail, hrest, htail, hmask⟩ := ih hr₀
        exact ⟨x :: block, tail, by rw [hrest]; rfl, by rw [htail]; rfl,
          by rw [support_cons, hmask]⟩
      · exact absurd h (by simp)

/-- `moveLeft`: the gate after the first `m` gates crosses them when its
support is disjoint from theirs. -/
def crossLeft (m : ℕ) (rest : Circuit n) : Option (Circuit n) :=
  match pullBlock m rest with
  | some r => if masksDisjoint r.gate.support r.mask then some (r.gate :: r.tail) else none
  | none => none

lemma crossLeft_sound {m : ℕ} {c c' : Circuit n} (h : crossLeft m c = some c') : c ≡ᵤ c' := by
  unfold crossLeft at h
  split at h
  · next r hr =>
    split at h
    · next hm =>
      cases h
      obtain ⟨block, tail, hrest, htail, hmask⟩ := pullBlock_spec hr
      subst hrest
      rw [htail]
      have hg := gate_block_comm_of_disjoint r.gate block (hmask ▸ masksDisjoint_iff.mp hm)
      calc block ++ r.gate :: tail = (block ++ [r.gate]) ++ tail := by simp
        _ ≡ᵤ ([r.gate] ++ block) ++ tail := hg.symm.append (Equivalent.refl tail)
        _ = r.gate :: (block ++ tail) := rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Push `g` past the first `k` gates: one pass that folds their support
and rebuilds them in front of `g`. -/
def pushBlock (g : Instr n) : ℕ → Circuit n → Option (ℕ × Circuit n)
  | 0, rest => some (0, g :: rest)
  | k + 1, x :: rest =>
    match pushBlock g k rest with
    | some p => some (x.support ||| p.1, x :: p.2)
    | none => none
  | _ + 1, [] => none

/-- What `pushBlock` computes, as a split of its input. -/
lemma pushBlock_spec {g : Instr n} {k : ℕ} {c : Circuit n} {p : ℕ × Circuit n}
    (h : pushBlock g k c = some p) :
    ∃ block tail, c = block ++ tail ∧ p.2 = block ++ g :: tail ∧ p.1 = support block := by
  induction k generalizing c p with
  | zero =>
    rw [pushBlock] at h
    cases h
    exact ⟨[], c, rfl, rfl, rfl⟩
  | succ k ih =>
    cases c with
    | nil => exact absurd h (by simp [pushBlock])
    | cons x rest =>
      rw [pushBlock] at h
      split at h
      · next p₀ hp₀ =>
        cases h
        obtain ⟨block, tail, hrest, htail, hmask⟩ := ih hp₀
        exact ⟨x :: block, tail, by rw [hrest]; rfl, by rw [htail]; rfl,
          by rw [support_cons, hmask]⟩
      · exact absurd h (by simp)

/-- `moveRight`: the first gate crosses the `d` gates after it when its
support is disjoint from theirs. -/
def crossRight (d : ℕ) : Circuit n → Option (Circuit n)
  | g :: rest =>
    match pushBlock g d rest with
    | some p => if masksDisjoint g.support p.1 then some p.2 else none
    | none => none
  | [] => none

lemma crossRight_sound {d : ℕ} {c c' : Circuit n} (h : crossRight d c = some c') : c ≡ᵤ c' := by
  unfold crossRight at h
  split at h
  · next g rest =>
    split at h
    · next p hp =>
      split at h
      · next hm =>
        cases h
        obtain ⟨block, tail, hrest, htail, hmask⟩ := pushBlock_spec hp
        subst hrest
        rw [htail]
        have hg := gate_block_comm_of_disjoint g block (hmask ▸ masksDisjoint_iff.mp hm)
        calc g :: (block ++ tail) = ([g] ++ block) ++ tail := rfl
          _ ≡ᵤ (block ++ [g]) ++ tail := hg.append (Equivalent.refl tail)
          _ = block ++ g :: tail := by simp
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The `k`-th checker of a table row. -/
def nthChecker {k : ℕ} : List (Checker k) → ℕ → Option (Checker k)
  | [], _ => none
  | C :: _, 0 => some C
  | _ :: Cs, j + 1 => nthChecker Cs j

/-- `window`: replace the placed `a` in front by the placed `b` when
`wires` has no duplicate and checker `k` accepts `(a, b)`. -/
def windowFront (Cs : CheckerTable) (wires : List (Fin n)) (a b : Circuit wires.length)
    (k : ℕ) (rest : Circuit n) : Option (Circuit n) :=
  if h : wires.Nodup then
    if rest.take a.length = rename (wiresOf wires h) a then
      match nthChecker (Cs wires.length) k with
      | some C =>
        if C.check a b then some (rename (wiresOf wires h) b ++ rest.drop a.length) else none
      | none => none
    else none
  else none

lemma windowFront_sound {Cs : CheckerTable} {wires : List (Fin n)}
    {a b : Circuit wires.length} {k : ℕ} {c c' : Circuit n}
    (h : windowFront Cs wires a b k c = some c') : c ≡ᵤ c' := by
  unfold windowFront at h
  split at h
  · next hnd =>
    split at h
    · next hseg =>
      split at h
      · next C _ =>
        split at h
        · next hC =>
          cases h
          calc c = c.take a.length ++ c.drop a.length := (List.take_append_drop _ c).symm
            _ = rename (wiresOf wires hnd) a ++ c.drop a.length := by rw [hseg]
            _ ≡ᵤ rename (wiresOf wires hnd) b ++ c.drop a.length :=
              ((C.sound a b hC).rename _).append (Equivalent.refl _)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### Replay -/

/-- Run one step; `none` if it is not licensed. `moveLeft i d` walks to
position `i - d` and crosses `min d i` gates; every other step walks to
its position. -/
def replayStep (Cs : CheckerTable) (c : Circuit n) : Step n → Option (Circuit n)
  | .swap i => rewriteAt swapFront i c
  | .moveLeft i d => rewriteAt (crossLeft (i - (i - d))) (i - d) c
  | .moveRight i d => rewriteAt (crossRight d) i c
  | .cancel i => rewriteAt cancelFront i c
  | .insert i a b => rewriteAt (insertFront a b) i c
  | .window i wires a b k => rewriteAt (windowFront Cs wires a b k) i c

/-- Every licensed step preserves equivalence. -/
theorem replayStep_sound {Cs : CheckerTable} {c c' : Circuit n} {s : Step n}
    (h : replayStep Cs c s = some c') : c ≡ᵤ c' := by
  cases s with
  | swap i => exact rewriteAt_sound (fun h => swapFront_sound h) h
  | moveLeft i d => exact rewriteAt_sound (fun h => crossLeft_sound h) h
  | moveRight i d => exact rewriteAt_sound (fun h => crossRight_sound h) h
  | cancel i => exact rewriteAt_sound (fun h => cancelFront_sound h) h
  | insert i a b => exact rewriteAt_sound (fun h => insertFront_sound h) h
  | window i wires a b k => exact rewriteAt_sound (fun h => windowFront_sound h) h

/-- Run a certificate; `none` as soon as a step is not licensed. -/
def replay (Cs : CheckerTable) : List (Step n) → Circuit n → Option (Circuit n)
  | [], c => some c
  | s :: steps, c =>
    match replayStep Cs c s with
    | some c' => replay Cs steps c'
    | none => none

/-- A replayed certificate is a proof: the output is equivalent to the
input, for every checker table. This is the only theorem a certificate
needs; the kernel's work is the evaluation of `replay`. -/
theorem replay_sound (Cs : CheckerTable) (steps : List (Step n)) {c c' : Circuit n}
    (h : replay Cs steps c = some c') : c ≡ᵤ c' := by
  induction steps generalizing c with
  | nil =>
    cases h
    exact Equivalent.refl _
  | cons s steps ih =>
    unfold replay at h
    split at h
    · next c₁ hs => exact (replayStep_sound hs).trans (ih h)
    · exact absurd h (by simp)

/-! ### The default table and the closing form -/

/-- The default checker table: index `0` is the basis evaluator (cost
`2 ^ k` for a window on `k` wires), index `1` is syntactic equality. -/
def defaultCheckers : CheckerTable := fun k => [evalChecker k, syntacticChecker k]

/-- Close a goal `c₁ ≡ᵤ c₂` by replaying a certificate:
`circuit_replay Cs steps` is `replay_sound Cs steps (by decide +kernel)`,
so the kernel evaluates `replay Cs steps c₁` once and compares the result
with `c₂`. -/
macro "circuit_replay " Cs:term:max steps:term:max : tactic =>
  `(tactic| exact replay_sound $Cs $steps (by decide +kernel))

end Quantum.Circuit
