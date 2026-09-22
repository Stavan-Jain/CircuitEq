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
checkers a window may name by index. Every certified checker written
against `CircuitEq.Checker` can be added to a table, and `replay_sound`
holds for every table because each checker carries its own proof. This
file imports no checker; the tables the tactics use, `defaultCheckers` and
`defaultPhaseFinders`, are in `CircuitEq.Defaults`.

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
way. Long exact traces are split into bounded replay declarations and
composed by `Equivalent.trans`; the tactic caches separately checked
windows with `Checker.ofProof` and `CheckerTable.cache`. The manual macro
still runs the trace in one declaration.

## Up to a global phase

The same steps prove `c₁ ≡ₚ[k] c₂` and `c₁ ≡ₚ c₂`. `replayPhase Fs steps c₁`
reads a `window` against a `PhaseTable` of `PhaseFinder`s: the finder names
the exponent `q` with `a ≡ₚ[q] b` on the window's wires, the interpreter
adds the exponents up in `Fin 8`, and the result is `some (k, c₂)`.
`replayPhase_sound` concludes `c₁ ≡ₚ[k] c₂`, `replayUpToPhase_sound`
forgets `k`, and `circuit_replay_phase defaultPhaseFinders steps` closes
either goal. The step data is the same for all three relations; only the
reading of `window` differs. See the section "Replay up to a global phase"
below.

`Step` and `replay` are meant to be mirrored outside Lean, so that a search
can run the same interpreter fast and hand Lean only the data
(`scripts/certificate.py`); a step the mirror accepts and `replay` rejects
is a bug in the mirror, never a soundness problem.

## Kernel cost

A step costs one pass over the prefix before its position plus one over the
block it crosses, at roughly 20–30 µs per list cell in the kernel (structural
recursion unfolds through `brecOn`), so a trace of `s` moves on a circuit of `m`
gates costs `O(s · m)` (measured in `benchmarks/scale/README.md`, "Where each
tool stands"). Windows cost their checker, `2 ^ k` for the evaluator on `k`
wires, and dominate real benchmarks. The next lever for long circuits is a `Nat`
encoding of the instruction list, on which a move is a handful of
GMP-accelerated bit operations instead of a walk. -/

namespace Quantum.Circuit

variable {n : ℕ}

/-- A checker table: for each register size `k`, the checkers a `window`
step may name by index. -/
abbrev CheckerTable := (k : ℕ) → List (Checker k)

/-- Prepend a proved window to the row for its own register size. Other
rows are unchanged. This lets a bounded replay reuse a separately checked
window through the ordinary checker contract. -/
def CheckerTable.cache (Cs : CheckerTable) {m : ℕ} (a b : Circuit m)
    (hab : a ≡ᵤ b) : CheckerTable := fun k =>
  if h : m = k then (h ▸ Checker.ofProof a b hab) :: Cs k else Cs k

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

/-- A local rewrite that establishes a relation does so at any position,
for every relation that prepending a gate preserves: `≡ᵤ`, and `≡ₚ[k]`
for the replay up to a global phase. -/
lemma rewriteAt_rel {R : Circuit n → Circuit n → Prop}
    (hcons : ∀ (g : Instr n) {c c' : Circuit n}, R c c' → R (g :: c) (g :: c'))
    {f : Circuit n → Option (Circuit n)}
    (hf : ∀ {rest rest' : Circuit n}, f rest = some rest' → R rest rest') {k : ℕ}
    {c c' : Circuit n} (h : rewriteAt f k c = some c') : R c c' := by
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
        exact hcons g (ih hc₀)
      · exact absurd h (by simp)

/-- A local rewrite that preserves equivalence does so at any position. -/
lemma rewriteAt_sound {f : Circuit n → Option (Circuit n)}
    (hf : ∀ {rest rest' : Circuit n}, f rest = some rest' → rest ≡ᵤ rest') {k : ℕ}
    {c c' : Circuit n} (h : rewriteAt f k c = some c') : c ≡ᵤ c' :=
  rewriteAt_rel (R := Equivalent) (fun g => Equivalent.cons g) (fun h => hf h) h

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

lemma crossRight_sound {d : ℕ} {c c' : Circuit n} (h : crossRight d c = some c') :
    c ≡ᵤ c' := by
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

/-- The `k`-th entry of a table row, a checker or a phase finder. -/
def nthEntry {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | C :: _, 0 => some C
  | _ :: Cs, j + 1 => nthEntry Cs j

/-- `window`: replace the placed `a` in front by the placed `b` when
`wires` has no duplicate and checker `k` accepts `(a, b)`. -/
def windowFront (Cs : CheckerTable) (wires : List (Fin n)) (a b : Circuit wires.length)
    (k : ℕ) (rest : Circuit n) : Option (Circuit n) :=
  if h : wires.Nodup then
    if rest.take a.length = rename (wiresOf wires h) a then
      match nthEntry (Cs wires.length) k with
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

/-- Run one step that is not a `window`: the exact rewrites, which every
reading of a certificate shares. `none` if the step is not licensed, and
for a `window`, which each reading interprets itself. `moveLeft i d` walks
to position `i - d` and crosses `min d i` gates; every other step walks to
its position. -/
def exactStep (c : Circuit n) : Step n → Option (Circuit n)
  | .swap i => rewriteAt swapFront i c
  | .moveLeft i d => rewriteAt (crossLeft (i - (i - d))) (i - d) c
  | .moveRight i d => rewriteAt (crossRight d) i c
  | .cancel i => rewriteAt cancelFront i c
  | .insert i a b => rewriteAt (insertFront a b) i c
  | .window .. => none

/-- Every licensed exact step preserves equivalence. -/
theorem exactStep_sound {c c' : Circuit n} {s : Step n}
    (h : exactStep c s = some c') : c ≡ᵤ c' := by
  cases s with
  | swap i => exact rewriteAt_sound (fun h => swapFront_sound h) h
  | moveLeft i d => exact rewriteAt_sound (fun h => crossLeft_sound h) h
  | moveRight i d => exact rewriteAt_sound (fun h => crossRight_sound h) h
  | cancel i => exact rewriteAt_sound (fun h => cancelFront_sound h) h
  | insert i a b => exact rewriteAt_sound (fun h => insertFront_sound h) h
  | window i wires a b k => exact absurd h (by simp [exactStep])

/-- Run one step; `none` if it is not licensed. A `window` is decided by
checker `k` of the table; every other step is `exactStep`. -/
def replayStep (Cs : CheckerTable) (c : Circuit n) : Step n → Option (Circuit n)
  | .window i wires a b k => rewriteAt (windowFront Cs wires a b k) i c
  | s => exactStep c s

/-- Every licensed step preserves equivalence. -/
theorem replayStep_sound {Cs : CheckerTable} {c c' : Circuit n} {s : Step n}
    (h : replayStep Cs c s = some c') : c ≡ᵤ c' := by
  cases s
  case window i wires a b k => exact rewriteAt_sound (fun h => windowFront_sound h) h
  all_goals exact exactStep_sound (by simpa only [replayStep] using h)

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

/-! ### Replay up to a global phase

Optimisers preserve a circuit up to a global phase, and the phase appears
inside a window: `Z X` against `X Z` is `ω ^ 4`. `replayPhase` reads the
same `Step`s with one change. A `window` names a `PhaseFinder` of a
`PhaseTable` instead of a `Checker`; the finder answers with the exponent
`q` for which `a ≡ₚ[q] b` on the window's own wires, and the interpreter
adds it to the phase accumulated so far. Every other step is the exact
rewrite of `replayStep` and leaves the phase alone. Placement keeps a
window's phase (`EquivalentWithPhase.rename`) and so do the gates around it
(`EquivalentWithPhase.cons`, `append_right`), so the sum of the window
phases is the phase of the whole: `replayPhase_sound` concludes
`c ≡ₚ[k] c'` with `k` computed by the kernel, and `replayUpToPhase_sound`
forgets it and concludes `c ≡ₚ c'`. A certificate for `≡ᵤ` replays here
with phase `0` under a table of `Checker.toFinder`s.

The phase travels as an accumulator so that the interpreter stays a loop,
and it is matched out of each step's result rather than projected: a step
that is not a window hands back the very term it was given, so the chain
of pending additions the kernel evaluates at the end is as long as the
number of windows, not the number of steps. -/

/-- A phase table: for each register size `k`, the phase finders a `window`
step may name by index when a certificate is replayed up to a global
phase. -/
abbrev PhaseTable := (k : ℕ) → List (PhaseFinder k)

/-- The phase of a window on its own wires: what finder number `k` of the
table's row for that register finds. -/
def windowPhase (Fs : PhaseTable) {m : ℕ} (a b : Circuit m) (k : ℕ) : Option (Fin 8) :=
  match nthEntry (Fs m) k with
  | some F => F.find a b
  | none => none

/-- A window's phase, once found, is proved. -/
lemma windowPhase_sound {Fs : PhaseTable} {m : ℕ} {a b : Circuit m} {k : ℕ} {q : Fin 8}
    (h : windowPhase Fs a b k = some q) : a ≡ₚ[q] b := by
  unfold windowPhase at h
  split at h
  · next F _ => exact F.sound a b q h
  · exact absurd h (by simp)

/-- The syntactic half of a `window` step, no checker consulted: when
`wires` has no duplicate and the circuit starts with the placed `a`,
replace it by the placed `b`. -/
def placeFront (wires : List (Fin n)) (a b : Circuit wires.length) (rest : Circuit n) :
    Option (Circuit n) :=
  if h : wires.Nodup then
    if rest.take a.length = rename (wiresOf wires h) a then
      some (rename (wiresOf wires h) b ++ rest.drop a.length)
    else none
  else none

/-- A placed window relates the circuits as its two sides are related on
their own wires, with the same phase. -/
lemma placeFront_sound {wires : List (Fin n)} {a b : Circuit wires.length} {q : Fin 8}
    (hab : a ≡ₚ[q] b) {c c' : Circuit n} (h : placeFront wires a b c = some c') :
    c ≡ₚ[q] c' := by
  unfold placeFront at h
  split at h
  · next hnd =>
    split at h
    · next hseg =>
      cases h
      calc c = c.take a.length ++ c.drop a.length := (List.take_append_drop _ c).symm
        _ = rename (wiresOf wires hnd) a ++ c.drop a.length := by rw [hseg]
        _ ≡ₚ[q] rename (wiresOf wires hnd) b ++ c.drop a.length :=
          (hab.rename _).append_right _
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Run one step up to a global phase, from the phase `p` accumulated so
far: `none` if the step is not licensed, otherwise the new phase and the
rewritten circuit. A `window` is placed syntactically and adds the phase
its finder names; every other step is `exactStep` and hands `p` back
untouched. -/
def replayStepPhase (Fs : PhaseTable) (p : Fin 8) (c : Circuit n) :
    Step n → Option (Fin 8 × Circuit n)
  | .window i wires a b k =>
    match rewriteAt (placeFront wires a b) i c with
    | some c' =>
      match windowPhase Fs a b k with
      | some q => some (p + q, c')
      | none => none
    | none => none
  | s => (exactStep c s).map (Prod.mk p)

/-- An exact step, read as a step up to phase, keeps the accumulated
phase. -/
lemma exactStep_phase_sound {s : Step n} {p q : Fin 8} {c₀ c c' : Circuit n}
    (h₀ : c₀ ≡ₚ[p] c) (h : (exactStep c s).map (Prod.mk p) = some (q, c')) :
    c₀ ≡ₚ[q] c' := by
  obtain ⟨c₁, hc₁, heq⟩ := Option.map_eq_some_iff.1 h
  cases heq
  exact h₀.trans_equivalent (exactStep_sound hc₁)

/-- Every licensed step extends an equivalence with a named phase: if `c₀`
is `ω ^ p` times `c`, and the step takes `(p, c)` to `(q, c')`, then `c₀`
is `ω ^ q` times `c'`. -/
theorem replayStepPhase_sound {Fs : PhaseTable} {p q : Fin 8} {c₀ c c' : Circuit n}
    {s : Step n} (h₀ : c₀ ≡ₚ[p] c) (h : replayStepPhase Fs p c s = some (q, c')) :
    c₀ ≡ₚ[q] c' := by
  cases s
  case window i wires a b k =>
    rw [replayStepPhase] at h
    split at h
    · next c₁ hc₁ =>
      split at h
      · next r hr =>
        cases h
        exact h₀.trans (rewriteAt_rel (R := EquivalentWithPhase r)
          (fun g => EquivalentWithPhase.cons g)
          (fun h => placeFront_sound (windowPhase_sound hr) h) hc₁)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  all_goals exact exactStep_phase_sound h₀ (by simpa only [replayStepPhase] using h)

/-- Run a certificate up to a global phase, from the phase `p` accumulated
so far; `none` as soon as a step is not licensed. -/
def replayPhaseFrom (Fs : PhaseTable) :
    List (Step n) → Fin 8 → Circuit n → Option (Fin 8 × Circuit n)
  | [], p, c => some (p, c)
  | s :: steps, p, c =>
    match replayStepPhase Fs p c s with
    | some (q, c') => replayPhaseFrom Fs steps q c'
    | none => none

/-- A replay from `(p, c)` extends an equivalence with phase `p`. -/
lemma replayPhaseFrom_sound {Fs : PhaseTable} {steps : List (Step n)} {p q : Fin 8}
    {c₀ c c' : Circuit n} (h₀ : c₀ ≡ₚ[p] c) (h : replayPhaseFrom Fs steps p c = some (q, c')) :
    c₀ ≡ₚ[q] c' := by
  induction steps generalizing p c with
  | nil =>
    cases h
    exact h₀
  | cons s steps ih =>
    unfold replayPhaseFrom at h
    split at h
    · next r c₁ hs => exact ih (replayStepPhase_sound h₀ hs) h
    · exact absurd h (by simp)

/-- Run a certificate up to a global phase: the exponent of the phase the
windows add up to, and the resulting circuit; `none` as soon as a step is
not licensed. -/
def replayPhase (Fs : PhaseTable) (steps : List (Step n)) (c : Circuit n) :
    Option (Fin 8 × Circuit n) :=
  replayPhaseFrom Fs steps 0 c

/-- A certificate replayed up to phase is a proof, and it names the phase:
the input is `ω ^ k` times the output, for every phase table. The kernel's
work is the evaluation of `replayPhase`, which computes `k`. -/
theorem replayPhase_sound (Fs : PhaseTable) (steps : List (Step n)) {k : Fin 8}
    {c c' : Circuit n} (h : replayPhase Fs steps c = some (k, c')) : c ≡ₚ[k] c' :=
  replayPhaseFrom_sound (EquivalentWithPhase.refl c) h

/-- `replayPhase` with the phase forgotten: the circuit a certificate ends
in when its windows hold up to a global phase. -/
def replayUpToPhase (Fs : PhaseTable) (steps : List (Step n)) (c : Circuit n) :
    Option (Circuit n) :=
  match replayPhase Fs steps c with
  | some r => some r.2
  | none => none

/-- A certificate replayed up to phase proves equivalence up to a global
phase, for every phase table. This is the closing form for a goal
`c ≡ₚ c'`, where the phase need not be known in advance. -/
theorem replayUpToPhase_sound (Fs : PhaseTable) (steps : List (Step n)) {c c' : Circuit n}
    (h : replayUpToPhase Fs steps c = some c') : c ≡ₚ c' := by
  unfold replayUpToPhase at h
  split at h
  · next r hr =>
    cases h
    exact (replayPhase_sound Fs steps (k := r.1) hr).toUpToPhase
  · exact absurd h (by simp)

/-! ### The closing forms -/

/-- Close a goal `c₁ ≡ᵤ c₂` by replaying a certificate:
`circuit_replay Cs steps` is `replay_sound Cs steps (by decide +kernel)`,
so the kernel evaluates `replay Cs steps c₁` once and compares the result
with `c₂`. -/
macro "circuit_replay " Cs:term:max steps:term:max : tactic =>
  `(tactic| exact replay_sound $Cs $steps (by decide +kernel))

/-- Close a goal `c₁ ≡ₚ[k] c₂` or `c₁ ≡ₚ c₂` by replaying a certificate up
to a global phase: `circuit_replay_phase Fs steps` is
`replayPhase_sound Fs steps (by decide +kernel)` for a named phase, where
the kernel evaluates `replayPhase Fs steps c₁` once and compares the result
with `(k, c₂)`, and `replayUpToPhase_sound Fs steps (by decide +kernel)`
otherwise. -/
macro "circuit_replay_phase " Fs:term:max steps:term:max : tactic =>
  `(tactic| (
    first
    | apply replayPhase_sound $Fs $steps
    | apply replayUpToPhase_sound $Fs $steps
    decide +kernel))

end Quantum.Circuit
