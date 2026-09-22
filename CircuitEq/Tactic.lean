/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Defaults
import Lean

/-! # Circuit tactics: `circuit_simp` and `circuit_windows`

Both tactics prove goals `c₁ ≡ᵤ c₂` between concrete instruction lists by
searching, in meta code, for a certificate (`CircuitEq.Certificate`): a
list of `Step`s whose replay turns `c₁` into `c₂`. The goal is closed by
one application of `replay_sound` to a kernel evaluation of `replay`, so
the proof term is constant-size and the kernel's work is one check per
step. No state vector is ever evaluated on the full register: windows are
decided on their own wires by the checker table `defaultCheckers`.

Both also accept a goal up to a global phase, `c₁ ≡ₚ c₂` or, with the
exponent named, `c₁ ≡ₚ[k] c₂`. The search and the certificate are the
same; the trace is replayed by `replayPhase` under `defaultPhaseFinders`
and the goal is closed by `replayUpToPhase_sound` or `replayPhase_sound`.
Each window may then hold only up to a phase of its own (`Z X` against
`X Z` is `ω ^ 4`): the basis evaluator names it on the window's wires, the
kernel adds the windows' phases up, and a goal `c₁ ≡ₚ[k] c₂` checks the
sum against `k`. Every move outside a window is still an exact commutation
or cancellation.

* `circuit_simp` cancels checked inverse pairs through the gates they
  commute with, then aligns the two lists by pulling each gate of `c₂` to
  the front of what remains of `c₁` through the gates before it. A pull is
  a `moveLeft` across the gates on other wires, licensed by one bitmask
  test, plus a `swap` for each gate on a shared wire that
  `Instr.CanCommute` licenses.

* `circuit_windows [(a₁, b₁), …, (aₘ, bₘ)]` is the window pattern of the
  roadmap: the alignment is input, the tactic checks it. A window `aᵢ ↔ bᵢ`
  is a pair of gate lists on the full register that touch a few wires. The
  tactic restricts the pair to those wires and emits a `window` step, which
  `replay` checks with the basis evaluator at cost `2 ^ k` for `k` wires,
  and walks `c₂` in order: at each point it pulls the next window to the
  front of both circuits if its gates can be moved there, otherwise the
  next gate of `c₂` is context and is pulled to the front of `c₁`. Windows
  are consumed in the listed order. A window with an empty side is a
  deletion or an insertion; a window whose sides are the same gates in
  different orders is a commutation the syntactic check does not know.

The search runs on both circuits. Moves found on `c₂` are appended to the
trace in reverse as their inverses (`moveRight` for `moveLeft`, `insert`
for `cancel`), so the certificate is a single trace from `c₁` to `c₂`.

Neither tactic searches for an alignment. A move the checks do not license
fails in the search, naming the offending instruction; a false window is
refused by `replay`, and the tactic then reports the window the kernel
refutes on its own wires. `set_option trace.circuit.certificate true`
prints the certificate a tactic found, in the syntax `circuit_replay`
accepts, so a proof can be kept as data or compared with an external
search's output.
-/

namespace Quantum.Circuit.Tactic

open Lean Meta Elab Tactic

initialize registerTraceClass `circuit.certificate

/-! ### Reading circuits -/

/-- Read a reducible list while leaving its elements symbolic. -/
private partial def readList (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match_expr e with
  | List.nil _ => return []
  | List.cons _ a as => return a :: (← readList as)
  | _ => throwError "expected a list that unfolds to its elements, got{indentExpr e}"

/-- An instruction as data: the gate's constructor name and its wires. -/
private inductive MInstr where
  | one (g : Name) (i : Nat)
  | cnot (c t : Nat)
  deriving BEq, Inhabited

/-- The wires of an instruction. -/
private def MInstr.wires : MInstr → List Nat
  | .one _ i => [i]
  | .cnot c t => [c, t]

/-- An instruction in the readable constructor syntax, `T 0` or `CX 1 3`. -/
private def MInstr.format : MInstr → String
  | .one g i => s!"{g.getString!} {i}"
  | .cnot c t => s!"CX {c} {t}"

/-- A circuit in the readable syntax. -/
private def formatCircuit (c : List MInstr) : String :=
  "[" ++ ", ".intercalate (c.map MInstr.format) ++ "]"

/-- A gate of a circuit being aligned: its expression, its reading, and
the `Fin n` expressions of its wires, for building placed windows. -/
private structure Gate where
  /-- The instruction as an expression. -/
  e : Expr
  /-- The instruction as data. -/
  instr : MInstr
  /-- The wire expressions, in the order of `instr.wires`. -/
  wireExprs : List Expr
  deriving Inhabited

/-- Two gates on disjoint wires; the meta side of `masksDisjoint`. -/
private def Gate.disjoint (a b : Gate) : Bool :=
  a.instr.wires.all fun w => !(b.instr.wires.contains w)

/-- Two gates on the same set of wires; a necessary condition for
`Instr.CanCancel`. -/
private def Gate.sameWires (a b : Gate) : Bool :=
  a.instr.wires.all (b.instr.wires.contains ·) && b.instr.wires.all (a.instr.wires.contains ·)

/-- Read a concrete wire index. -/
private def readWire (w : Expr) : MetaM Nat := do
  let w' ← whnf w
  let_expr Fin.mk _ v _ := w' | throwError "not a concrete wire:{indentExpr w}"
  match ← (evalNat v).run with
  | some k => return k
  | none => throwError "not a concrete wire:{indentExpr w}"

/-- Read an instruction. -/
private def readGate (e : Expr) : MetaM Gate := do
  let e' ← whnf e
  match_expr e' with
  | Instr.one _ g i =>
    let .const gn _ ← whnf g | throwError "not a concrete gate:{indentExpr g}"
    return { e, instr := .one gn (← readWire i), wireExprs := [i] }
  | Instr.cnot _ c t =>
    return { e, instr := .cnot (← readWire c) (← readWire t), wireExprs := [c, t] }
  | _ => throwError "not an instruction:{indentExpr e}"

/-- Read a circuit. -/
private def readCircuit (e : Expr) : MetaM (Array Gate) :=
  return (← (← readList e).mapM readGate).toArray

/-- Whether a concrete decidable proposition evaluates to true. -/
private def decides (p : Expr) : MetaM Bool := do
  isDefEq (← mkDecide p) (mkConst ``Bool.true)

/-! ### Steps in meta form -/

/-- A certificate step in meta form; `cancel` keeps its pair so that a step
found on the right-hand circuit can be inverted. -/
private inductive MStep where
  | swap (i : Nat)
  | moveLeft (i d : Nat)
  | moveRight (i d : Nat)
  | cancel (i : Nat) (a b : Expr)
  | insert (i : Nat) (a b : Expr)
  | window (i : Nat) (wires a b : Expr) (k : Nat) (wireNums : List Nat) (aData bData : List MInstr)

/-- The `Step n` expression of a meta step. -/
private def MStep.toExpr (n : Expr) : MStep → Expr
  | .swap i => mkApp2 (mkConst ``Step.swap) n (mkNatLit i)
  | .moveLeft i d => mkApp3 (mkConst ``Step.moveLeft) n (mkNatLit i) (mkNatLit d)
  | .moveRight i d => mkApp3 (mkConst ``Step.moveRight) n (mkNatLit i) (mkNatLit d)
  | .cancel i _ _ => mkApp2 (mkConst ``Step.cancel) n (mkNatLit i)
  | .insert i a b => mkApp4 (mkConst ``Step.insert) n (mkNatLit i) a b
  | .window i wires a b k _ _ _ =>
    mkAppN (mkConst ``Step.window) #[n, mkNatLit i, wires, a, b, mkNatLit k]

/-- A meta step in the syntax `circuit_replay` accepts. -/
private def MStep.format : MStep → MessageData
  | .swap i => m!".swap {i}"
  | .moveLeft i d => m!".moveLeft {i} {d}"
  | .moveRight i d => m!".moveRight {i} {d}"
  | .cancel i _ _ => m!".cancel {i}"
  | .insert i a b => m!".insert {i} ({a}) ({b})"
  | .window i _ _ _ k wires a b =>
    m!".window {i} {wires} ({formatCircuit a} : Circuit {wires.length}) {formatCircuit b} {k}"

/-- The inverse of a step, for the moves found on the right-hand circuit;
a window is never found there. -/
private def MStep.invert : MStep → Option MStep
  | .swap i => some (.swap i)
  | .moveLeft i d => some (.moveRight (i - d) d)
  | .moveRight i d => some (.moveLeft (i + d) d)
  | .cancel i a b => some (.insert i a b)
  | .insert i a b => some (.cancel i a b)
  | .window .. => none

/-- Which circuit a search step acts on. Steps on the right are inverted
into the trace, so a `swap` there is checked in the orientation its inverse
will be checked in by `replay`. -/
private inductive Side where
  | left
  | right

/-! ### Pulling gates -/

/-- Move the gate at index `p` of `cur` to index `q ≤ p`, checking every
gate it crosses: a run of gates on other wires is one `moveLeft`, a gate
on a shared wire must pass `Instr.CanCommute` and is a `swap`. Fails at the
first gate the checks do not license. -/
private def pullTo (side : Side) (cur : Array Gate) (p q : Nat) :
    MetaM (Array Gate × Array MStep) := do
  let g := cur[p]!
  let mut steps : Array MStep := #[]
  let mut pos := p
  let mut run := 0
  for j' in [q:p] do
    let j := p - 1 - (j' - q)
    let x := cur[j]!
    if g.disjoint x then
      run := run + 1
    else
      if run > 0 then
        steps := steps.push (.moveLeft pos run)
        pos := pos - run
        run := 0
      let prop ← match side with
        | .left => mkAppM ``Instr.CanCommute #[x.e, g.e]
        | .right => mkAppM ``Instr.CanCommute #[g.e, x.e]
      unless ← decides prop do
        throwError "{g.e} is blocked by {x.e}"
      steps := steps.push (.swap (pos - 1))
      pos := pos - 1
  if run > 0 then
    steps := steps.push (.moveLeft pos run)
  return ((cur.eraseIdx! p).insertIdx! q g, steps)

/-- Pull `g` to index `q` of `cur`: the first occurrence at or after `q`
whose crossings the checks license. Returns the new circuit and the steps,
or fails naming the gate. -/
private def pullOne (side : Side) (cur : Array Gate) (q : Nat) (g : Gate) :
    MetaM (Array Gate × Array MStep) := do
  let mut seen := false
  for p in [q:cur.size] do
    if cur[p]!.instr == g.instr then
      seen := true
      if let some r ← observing? (pullTo side cur p q) then
        return r
  let region := (cur.extract q cur.size).toList.map (·.e)
  if seen then
    throwError "{g.e} is blocked by a gate on its wires in{indentD (toMessageData region)}"
  else
    throwError "{g.e} does not occur in{indentD (toMessageData region)}"

/-! ### Cancellation -/

/-- Remove inverse pairs: each pair passing `Instr.CanCancel` whose second
gate can be moved next to the first. -/
private partial def cancelPairs (side : Side) (cur : Array Gate) :
    MetaM (Array Gate × Array MStep) := do
  for i in [:cur.size] do
    for j in [i + 1:cur.size] do
      let a := cur[i]!
      let b := cur[j]!
      unless a.sameWires b do continue
      unless ← decides (← mkAppM ``Instr.CanCancel #[a.e, b.e]) do continue
      if let some (cur', moves) ← observing? (pullTo side cur j (i + 1)) then
        let (rest, more) ← cancelPairs side ((cur'.eraseIdx! i).eraseIdx! i)
        return (rest, moves ++ #[.cancel i a.e b.e] ++ more)
  return (cur, #[])

/-! ### The goal's relation -/

/-- The relation a goal is stated on, which decides how the certificate is
replayed: exactly (`replay`), or up to a global phase (`replayPhase`), with
the phase left open or named by the goal. -/
private inductive GoalKind where
  /-- `c₁ ≡ᵤ c₂`. -/
  | exact
  /-- `c₁ ≡ₚ c₂`. -/
  | upToPhase
  /-- `c₁ ≡ₚ[k] c₂`, with the exponent `k : Fin 8` as an expression. -/
  | withPhase (k : Expr)

/-- Whether windows are decided up to a global phase. -/
private def GoalKind.isPhase : GoalKind → Bool
  | .exact => false
  | _ => true

/-! ### Windows -/

/-- One window of an alignment: its two sides on the full register, and
the data of its `window` step: the wire list and both sides restricted to
those wires. -/
private structure Window where
  /-- The window's gates in the left circuit. -/
  left : Array Gate
  /-- The window's gates in the right circuit. -/
  right : Array Gate
  /-- The wires the window touches, as `List (Fin n)`. -/
  wires : Expr
  /-- The left side on its wires, as `Circuit wires.length`. -/
  a : Expr
  /-- The right side on its wires. -/
  b : Expr
  /-- `a ≡ᵤ b`, or `a ≡ₚ b` when the goal is up to a global phase, for the
  failure diagnosis. -/
  smallProp : Expr
  /-- The wire numbers, for printing. -/
  wireNums : List Nat
  /-- The left side on its wires, as data. -/
  aData : List MInstr
  /-- The right side on its wires, as data. -/
  bData : List MInstr

/-- Restrict a window to the wires it touches, in order of first use. -/
private def mkWindow (kind : GoalKind) (n : Expr) (left right : Array Gate) :
    MetaM Window := do
  let mut wires : Array (Nat × Expr) := #[]
  for g in left ++ right do
    for (w, we) in g.instr.wires.zip g.wireExprs do
      unless wires.any (·.1 == w) do
        wires := wires.push (w, we)
  let wiresE ← mkListLit (mkApp (mkConst ``Fin) n) (wires.toList.map (·.2))
  let k ← mkAppM ``List.length #[wiresE]
  let index (w : Nat) : MetaM Expr := do
    let some j := wires.findIdx? (·.1 == w) | throwError "wire {w} was not collected"
    let lt ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit j, k])
    mkAppM ``Fin.mk #[mkNatLit j, lt]
  let restrict (g : Gate) : MetaM Expr := do
    match g.instr with
    | .one gn i => mkAppM ``Instr.one #[mkConst gn, ← index i]
    | .cnot c t => mkAppM ``Instr.cnot #[← index c, ← index t]
  let pos (w : Nat) : Nat := (wires.findIdx? (·.1 == w)).getD 0
  let small (g : Gate) : MInstr :=
    match g.instr with
    | .one gn i => .one gn (pos i)
    | .cnot c t => .cnot (pos c) (pos t)
  let tyK := mkApp (mkConst ``Instr) k
  let a ← mkListLit tyK (← left.toList.mapM restrict)
  let b ← mkListLit tyK (← right.toList.mapM restrict)
  let smallProp ← mkAppM (if kind.isPhase then ``EquivalentUpToPhase else ``Equivalent) #[a, b]
  return { left, right, wires := wiresE, a, b, smallProp,
           wireNums := wires.toList.map (·.1), aData := left.toList.map small,
           bData := right.toList.map small }

/-- The gates of a window side, for messages. -/
private def sideMsg (gs : Array Gate) : MessageData := toMessageData (gs.toList.map (·.e))

/-! ### Alignment -/

/-- The search state: both circuits as rewritten so far, the length of
their agreed prefix, and the steps found on each side (those on the right
are forward steps on `c₂`, inverted when the trace is assembled). -/
private structure State where
  /-- The left circuit. -/
  left : Array Gate
  /-- The right circuit. -/
  right : Array Gate
  /-- The length of the agreed prefix. -/
  done : Nat
  /-- Steps on the left circuit. -/
  stepsL : Array MStep
  /-- Steps on the right circuit. -/
  stepsR : Array MStep

/-- Place window `w` at the agreed prefix: pull its left gates to the front
of the unconsumed left region and its right gates to the front of the
unconsumed right region, then emit the `window` step on the left. -/
private def placeWindow (w : Window) (st : State) : MetaM State := do
  let mut left := st.left
  let mut right := st.right
  let mut stepsL := st.stepsL
  let mut stepsR := st.stepsR
  for j in [:w.left.size] do
    let (l, s) ← pullOne .left left (st.done + j) w.left[j]!
    left := l
    stepsL := stepsL ++ s
  for j in [:w.right.size] do
    let (r, s) ← pullOne .right right (st.done + j) w.right[j]!
    right := r
    stepsR := stepsR ++ s
  stepsL := stepsL.push (.window st.done w.wires w.a w.b 0 w.wireNums w.aData w.bData)
  left := left.extract 0 st.done ++ w.right ++ left.extract (st.done + w.left.size) left.size
  return { left, right, done := st.done + w.right.size, stepsL, stepsR }

/-- Align the two circuits, consuming the windows from index `i` in order.
At each point the next window is placed if its gates can be moved to the
front of both unconsumed regions, otherwise the next gate of the right
circuit is context and is pulled to the front of the left one. -/
private partial def alignWindows (ws : Array Window) (i : Nat) (st : State) : MetaM State := do
  if h : i < ws.size then
    if let some st' ← observing? (placeWindow ws[i] st) then
      return ← alignWindows ws (i + 1) st'
  if st.done < st.right.size then
    let y := st.right[st.done]!
    let (left, s) ←
      try pullOne .left st.left st.done y
      catch e =>
        if h : i < ws.size then
          throwError "{e.toMessageData}\n(pending window {i + 1}: {sideMsg ws[i].left} ↔ \
            {sideMsg ws[i].right})"
        else
          throw e
    alignWindows ws i { st with left, stepsL := st.stepsL ++ s, done := st.done + 1 }
  else
    if h : i < ws.size then
      throwError "window {i + 1} could not be placed: {sideMsg ws[i].left} ↔ \
        {sideMsg ws[i].right}"
    unless st.left.size = st.done do
      let rest := (st.left.extract st.done st.left.size).toList.map (·.e)
      throwError "unmatched instructions on the left:{indentD (toMessageData rest)}"
    return st

/-! ### Closing the goal -/

/-- Read the goal `c₁ ≡ᵤ c₂`, `c₁ ≡ₚ c₂` or `c₁ ≡ₚ[k] c₂` and return its
relation, `n` and the two circuits. -/
private def readGoal : TacticM (GoalKind × Expr × Expr × Expr) := do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  match_expr target with
  | Equivalent n a b => return (.exact, n, a, b)
  | EquivalentUpToPhase n a b => return (.upToPhase, n, a, b)
  | EquivalentWithPhase n k a b =>
    if k.hasExprMVar then
      throwError "the phase of the goal is not determined: state the goal as c₁ ≡ₚ c₂, or name \
        the exponent in c₁ ≡ₚ[k] c₂ (a wrong exponent is answered with the right one)"
    return (.withPhase k, n, a, b)
  | _ =>
    throwError "expected a goal of the form c₁ ≡ᵤ c₂, c₁ ≡ₚ c₂ or c₁ ≡ₚ[k] c₂, \
      got{indentExpr target}"

/-- Prove a closed proposition by running a tactic on a fresh goal. -/
private def proveBy (p : Expr) (tac : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprMVar p
  let goals ← Lean.Elab.Tactic.run m.mvarId! (evalTactic tac)
  unless goals.isEmpty do throwError "could not prove{indentExpr p}"
  instantiateMVars m

/-- The proposition the kernel decides for a trace, and the proof of the
goal that a proof of it yields: `replay … = some b` with `replay_sound`,
`replayUpToPhase … = some b` with `replayUpToPhase_sound`, or
`replayPhase … = some (k, b)` with `replayPhase_sound`. -/
private def replayProp (kind : GoalKind) (n stepsE a b : Expr) :
    MetaM (Expr × (Expr → Expr)) := do
  match kind with
  | .exact =>
    let table := mkConst ``defaultCheckers
    let prop ← mkEq (mkApp4 (mkConst ``replay) n table stepsE a) (← mkAppM ``Option.some #[b])
    return (prop, fun h => mkAppN (mkConst ``replay_sound) #[n, table, stepsE, a, b, h])
  | .upToPhase =>
    let table := mkConst ``defaultPhaseFinders
    let prop ← mkEq (mkApp4 (mkConst ``replayUpToPhase) n table stepsE a)
      (← mkAppM ``Option.some #[b])
    return (prop, fun h => mkAppN (mkConst ``replayUpToPhase_sound) #[n, table, stepsE, a, b, h])
  | .withPhase k =>
    let table := mkConst ``defaultPhaseFinders
    let prop ← mkEq (mkApp4 (mkConst ``replayPhase) n table stepsE a)
      (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[k, b]])
    return (prop, fun h => mkAppN (mkConst ``replayPhase_sound) #[n, table, stepsE, k, a, b, h])

/-- Assemble the trace and close the goal by the soundness theorem of the
goal's relation applied to a kernel evaluation of the replay. If the kernel
refuses the trace, look for a window it refutes on its own wires and report
it; for a goal with a named phase, also check whether the trace replays
with a different phase, and name that one. -/
private def closeByReplay (kind : GoalKind) (n a b : Expr) (st : State) (ws : Array Window) :
    TacticM Unit := do
  let inverted ← st.stepsR.reverse.mapM fun s => do
    let some s' := s.invert | throwError "internal error: a window step on the right-hand circuit"
    return s'
  let steps := st.stepsL ++ inverted
  trace[circuit.certificate] "[{MessageData.joinSep (steps.toList.map MStep.format) ", "}]"
  let stepsE ← mkListLit (mkApp (mkConst ``Step) n) (steps.toList.map (·.toExpr n))
  let (prop, close) ← replayProp kind n stepsE a b
  let h ←
    try proveBy prop (← `(tactic| decide +kernel))
    catch e =>
      let upTo := if kind.isPhase then " up to a global phase" else ""
      for w in ws do
        let refuted ← observing? (proveBy (mkNot w.smallProp) (← `(tactic| decide +kernel)))
        if refuted.isSome then
          let mut hint : MessageData := ""
          unless kind.isPhase do
            let phaseProp ← mkAppM ``EquivalentUpToPhase #[w.a, w.b]
            if (← observing? (proveBy phaseProp (← `(tactic| decide +kernel)))).isSome then
              hint := "\nThe window does hold up to a global phase: state the goal as \
                c₁ ≡ₚ c₂ (or c₁ ≡ₚ[k] c₂) and this window is accepted."
          throwError "the window {sideMsg w.left} ↔ {sideMsg w.right} is not an \
            equivalence{upTo}: on its wires the kernel refutes{indentExpr w.smallProp}{hint}"
      if let .withPhase k := kind then
        let (open_, _) ← replayProp .upToPhase n stepsE a b
        if (← observing? (proveBy open_ (← `(tactic| decide +kernel)))).isSome then
          for j in [0:8] do
            let jE ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 8)) j
            let (named, _) ← replayProp (.withPhase jE) n stepsE a b
            if (← observing? (proveBy named (← `(tactic| decide +kernel)))).isSome then
              throwError "the circuits are equal up to the global phase ω ^ {j}, not \
                ω ^ {k}: the goal that holds is c₁ ≡ₚ[{j}] c₂"
      throwError "the certificate was not accepted by the replay:{indentExpr stepsE}\n\
        {e.toMessageData}"
  (← getMainGoal).assign (close h)
  replaceMainGoal []

/-! ### The tactics -/

/-- Cancel checked inverse pairs on both sides, then align the remainders
by checked commutations; the result is one certificate replayed by the
kernel. The goal is `c₁ ≡ᵤ c₂`; `c₁ ≡ₚ c₂` and `c₁ ≡ₚ[0] c₂` are accepted
too, and proved by the same exact moves. -/
elab "circuit_simp" : tactic => withMainContext do
  let (kind, n, a, b) ← readGoal
  let (left, stepsL) ← cancelPairs .left (← readCircuit a)
  let (right, stepsR) ← cancelPairs .right (← readCircuit b)
  let st ← alignWindows #[] 0 { left, right, done := 0, stepsL, stepsR }
  closeByReplay kind n a b st #[]

/-- Prove `c₁ ≡ᵤ c₂` from an alignment: a list of windows `(aᵢ, bᵢ)`, each
a pair of gate lists on the full register, in the order they occur. Each
window becomes a `window` step decided on its own wires; every other move
is a checked commutation.

On a goal `c₁ ≡ₚ c₂` each window need only hold up to a global phase of
its own, which the kernel finds on the window's wires; on `c₁ ≡ₚ[k] c₂` the
phases of the windows must add up to `k`, and if they add up to something
else the error names it. -/
elab "circuit_windows " ws:term : tactic => withMainContext do
  let (kind, n, a, b) ← readGoal
  let circ := mkApp (mkConst ``Quantum.Circuit) n
  let listTy ← mkAppM ``List #[← mkAppM ``Prod #[circ, circ]]
  let wsE ← instantiateMVars (← elabTermEnsuringType ws (some listTy))
  let mut windows : Array Window := #[]
  for p in ← readList wsE do
    let p ← whnf p
    let_expr Prod.mk _ _ l r := p | throwError "expected a pair of circuits, got{indentExpr p}"
    windows := windows.push (← mkWindow kind n (← readCircuit l) (← readCircuit r))
  let st ← alignWindows windows 0
    { left := ← readCircuit a, right := ← readCircuit b, done := 0, stepsL := #[], stepsR := #[] }
  closeByReplay kind n a b st windows

end Quantum.Circuit.Tactic
