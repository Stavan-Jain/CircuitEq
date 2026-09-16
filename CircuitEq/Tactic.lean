/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Rewriting
import CircuitEq.Embedding
import Lean

/-! # Circuit tactics: `circuit_simp` and `circuit_windows`

Both tactics prove goals `c₁ ≡ᵤ c₂` between concrete instruction lists by
assembling ordinary proof terms from `CircuitEq.Rewriting` and
`CircuitEq.Embedding`. The kernel checks every step, and no state vector is
ever evaluated on the full register.

* `circuit_simp` cancels checked inverse pairs through the gates they
  commute with (`cancel_window`), then aligns the two lists by pulling each
  gate of `c₂` to the front of what remains of `c₁` through a checked
  commuting prefix (`pull_cons`).

* `circuit_windows [(a₁, b₁), …, (aₘ, bₘ)]` is the window pattern of the
  roadmap: the alignment is input, the tactic checks it. A window `aᵢ ↔ bᵢ`
  is a pair of gate lists on the full register that touch a few wires. The
  tactic restricts the pair to those wires, decides the small equivalence
  by `decide +kernel` at cost `2 ^ k`, places it back with
  `Equivalent.of_rename`, and walks `c₂` in order: at each point it pulls
  the next window to the front of both circuits if its gates can be moved
  there, otherwise the next gate of `c₂` is context and is pulled to the
  front of `c₁`. Windows are consumed in the listed order. A window with an
  empty side is a deletion or an insertion; a window whose sides are the
  same gates in different orders is a commutation the syntactic check does
  not know.

Neither tactic searches. A move the decidable checks do not license fails
naming the offending instruction; a false window fails at its `decide`.
-/

namespace Quantum.Circuit.Tactic

open Lean Meta Elab Tactic

/-- Read a reducible list while leaving its elements symbolic. -/
private partial def readList (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match_expr e with
  | List.nil _ => return []
  | List.cons _ a as => return a :: (← readList as)
  | _ => throwError "expected a list that unfolds to its elements, got{indentExpr e}"

/-- Prove a concrete syntactic side condition by evaluation, or fail. -/
private def checkedDecision (p : Expr) : MetaM Expr := do
  let d ← mkDecide p
  unless ← isDefEq d (mkConst ``Bool.true) do
    throwError "cannot establish{indentExpr p}"
  mkDecideProof p

/-- Apply one decidable premise of a partially applied structural theorem. -/
private def discharge (e : Expr) : MetaM Expr := do
  let .forallE _ p _ _ ← whnf (← inferType e) | throwError "expected a proof premise"
  return mkApp e (← checkedDecision p)

/-- Prove a closed proposition by running a tactic on a fresh goal. -/
private def proveBy (p : Expr) (tac : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprMVar p
  let goals ← Lean.Elab.Tactic.run m.mvarId! (evalTactic tac)
  unless goals.isEmpty do throwError "could not prove{indentExpr p}"
  instantiateMVars m

/-- `Equivalent.trans` with the middle circuit given explicitly, so that the
kernel rather than the elaborator identifies `[a, b] ++ l` with
`a :: b :: l`. -/
private def mkTrans (n c₁ c₂ c₃ h₁ h₂ : Expr) : Expr :=
  mkAppN (mkConst ``Equivalent.trans) #[n, c₁, c₂, c₃, h₁, h₂]

/-! ### Cancellation -/

/-- Remove inverse pairs, recording a circuit-equivalence proof at each
step. -/
private partial def cancelPairs (ty : Expr) (xs : List Expr) : MetaM (List Expr × Expr) := do
  for i in [:xs.length] do
    for j in [i + 1:xs.length] do
      let attempt ← observing? do
        let a := xs[i]!
        let b := xs[j]!
        let pre ← mkListLit ty (xs.take i)
        let middle ← mkListLit ty ((xs.drop (i + 1)).take (j - i - 1))
        let tail ← mkListLit ty (xs.drop (j + 1))
        let step ← mkAppM ``cancel_window #[a, b, middle, tail]
        let step ← discharge (← discharge step)
        let empty ← mkListLit ty []
        let step ← mkAppM ``Equivalent.in_context #[step, pre, empty]
        let rest := xs.take i ++ (xs.drop (i + 1)).take (j - i - 1) ++ xs.drop (j + 1)
        let (ys, proof) ← cancelPairs ty rest
        return (ys, ← mkAppM ``Equivalent.trans #[step, proof])
      if let some result := attempt then return result
  return (xs, ← mkAppM ``Equivalent.refl #[← mkListLit ty xs])

/-! ### Pulling gates to the front -/

/-- Pull `g` to the front of `xs`: the first occurrence that passes the
commutation check against everything before it. Returns the rest of `xs`,
the split around the occurrence, and the proof of the check. -/
private def pullOne (ty g : Expr) (xs : List Expr) :
    MetaM (List Expr × Expr × Expr × Expr) := do
  let mut seen := false
  for i in [:xs.length] do
    if ← isDefEq xs[i]! g then
      seen := true
      let before ← mkListLit ty (xs.take i)
      let cond ← mkAppM ``Instr.CanCommuteAll #[g, before]
      if let some hc ← observing? (checkedDecision cond) then
        let after ← mkListLit ty (xs.drop (i + 1))
        return (xs.take i ++ xs.drop (i + 1), before, after, hc)
  if seen then
    throwError "{g} is blocked by a gate on its wires in{indentD (toMessageData xs)}"
  else
    throwError "{g} does not occur in{indentD (toMessageData xs)}"

/-- Pull the instructions of `gates`, in order, to the front of `xs`.
Returns the rest of `xs` and a proof of `xs ≡ᵤ gates ++ rest`. -/
private partial def pullMany (ty : Expr) (gates xs : List Expr) : MetaM (List Expr × Expr) := do
  match gates with
  | [] => return (xs, ← mkAppM ``Equivalent.refl #[← mkListLit ty xs])
  | g :: gates =>
    let (xs₁, before, after, hc) ← pullOne ty g xs
    let (rest, ht) ← pullMany ty gates xs₁
    let target ← mkListLit ty (gates ++ rest)
    let step ← mkAppM ``pull_cons #[g, before, after, target]
    return (rest, mkApp (mkApp step hc) ht)

/-! ### Windows -/

/-- One window of an alignment: its two sides as instruction lists on the
full register, and the proof that they are equivalent. -/
private structure Window where
  /-- The window's gates in the left circuit. -/
  left : List Expr
  /-- The window's gates in the right circuit. -/
  right : List Expr
  /-- A proof of `left ≡ᵤ right` on the full register. -/
  proof : Expr

/-- The wires an instruction touches. -/
private def instrWires (g : Expr) : MetaM (List Expr) := do
  let g ← whnf g
  match_expr g with
  | Instr.one _ _ i => return [i]
  | Instr.cnot _ c t => return [c, t]
  | _ => throwError "not an instruction:{indentExpr g}"

/-- Prove `a ≡ᵤ b` for a window: restrict both sides to the wires they
touch, decide the small equivalence in the kernel, and place it back on the
register with `Equivalent.of_rename`. -/
private def windowProof (n ty : Expr) (a b : List Expr) : TacticM Expr := do
  let mut wires : Array Expr := #[]
  for g in a ++ b do
    for w in ← instrWires g do
      unless ← wires.anyM (isDefEq · w) do
        wires := wires.push w
  let wireList ← mkListLit (mkApp (mkConst ``Fin) n) wires.toList
  let nodup ← checkedDecision (← mkAppM ``List.Nodup #[wireList])
  let f ← mkAppM ``wiresOf #[wireList, nodup]
  let k ← mkAppM ``List.length #[wireList]
  let index (w : Expr) : TacticM Expr := do
    for j in [:wires.size] do
      if ← isDefEq wires[j]! w then
        let lt ← checkedDecision (← mkAppM ``LT.lt #[mkNatLit j, k])
        return ← mkAppM ``Fin.mk #[mkNatLit j, lt]
    throwError "wire {w} was not collected"
  let restrict (g : Expr) : TacticM Expr := do
    let g ← whnf g
    match_expr g with
    | Instr.one _ gate i => mkAppM ``Instr.one #[gate, ← index i]
    | Instr.cnot _ c t => mkAppM ``Instr.cnot #[← index c, ← index t]
    | _ => throwError "not an instruction:{indentExpr g}"
  let tyK := mkApp (mkConst ``Instr) k
  let a' ← mkListLit tyK (← a.mapM restrict)
  let b' ← mkListLit tyK (← b.mapM restrict)
  let smallProp ← mkAppM ``Equivalent #[a', b']
  let small ←
    try proveBy smallProp (← `(tactic| decide +kernel))
    catch e =>
      let refuted ← observing? (proveBy (mkNot smallProp) (← `(tactic| decide +kernel)))
      if refuted.isSome then
        throwError "the window {a} ↔ {b} is not an equivalence: on its wires the kernel \
          refutes{indentExpr smallProp}"
      else
        throw e
  let placed (c' : Expr) (c : List Expr) : TacticM Expr := do
    let cE ← mkListLit ty c
    mkExpectedTypeHint (← mkEqRefl cE) (← mkEq (← mkAppM ``rename #[f, c']) cE)
  mkAppM ``Equivalent.of_rename #[f, small, ← placed a' a, ← placed b' b]

/-- Align `xs` with `ys`, consuming `ws` from index `i` in order; returns a
proof of `xs ≡ᵤ ys`. At each step the next window is pulled to the front
of both lists if its gates can be moved there, otherwise the next gate of
`ys` is context and is pulled to the front of `xs`. -/
private partial def alignWindows (n ty : Expr) (ws : Array Window) (i : Nat)
    (xs ys : List Expr) : MetaM Expr := do
  if h : i < ws.size then
    let w := ws[i]
    let pulled ← observing? do
      let (xs', pa) ← pullMany ty w.left xs
      let (ys', pb) ← pullMany ty w.right ys
      return (xs', pa, ys', pb)
    if let some (xs', pa, ys', pb) := pulled then
      let rest ← alignWindows n ty ws (i + 1) xs' ys'
      let mid ← mkAppM ``Equivalent.append #[w.proof, rest]
      let lx ← mkListLit ty (w.left ++ xs')
      let ry ← mkListLit ty (w.right ++ ys')
      let x ← mkListLit ty xs
      let y ← mkListLit ty ys
      let inner := mkTrans n lx ry y mid (← mkAppM ``Equivalent.symm #[pb])
      return mkTrans n x lx y pa inner
  match ys with
  | [] =>
    if h : i < ws.size then
      throwError "window {i + 1} could not be placed: {ws[i].left} ↔ {ws[i].right}"
    unless xs.isEmpty do
      throwError "unmatched instructions on the left:{indentD (toMessageData xs)}"
    mkAppM ``Equivalent.refl #[← mkListLit ty []]
  | y :: ys' =>
    let (xs', before, after, hc) ←
      try pullOne ty y xs
      catch e =>
        if h : i < ws.size then
          throwError "{e.toMessageData}\n(pending window {i + 1}: {ws[i].left} ↔ {ws[i].right})"
        else
          throw e
    let rest ← alignWindows n ty ws i xs' ys'
    let target ← mkListLit ty ys'
    let step ← mkAppM ``pull_cons #[y, before, after, target]
    return mkApp (mkApp step hc) rest

/-! ### The tactics -/

/-- Read the goal `c₁ ≡ᵤ c₂` and return `n`, the instruction type, and the
two circuits. -/
private def readGoal : TacticM (Expr × Expr × Expr × Expr) := do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let_expr Equivalent n a b := target |
    throwError "expected a goal of the form c₁ ≡ᵤ c₂, got{indentExpr target}"
  return (n, mkApp (mkConst ``Instr) n, a, b)

/-- Cancel checked inverse pairs on both sides, then align the remainders
by checked commutations. -/
elab "circuit_simp" : tactic => withMainContext do
  let (n, ty, a, b) ← readGoal
  let (as, ha) ← cancelPairs ty (← readList a)
  let (bs, hb) ← cancelPairs ty (← readList b)
  let hab ← alignWindows n ty #[] 0 as bs
  let proof ← mkAppM ``Equivalent.trans #[ha,
    ← mkAppM ``Equivalent.trans #[hab, ← mkAppM ``Equivalent.symm #[hb]]]
  (← getMainGoal).assign proof
  replaceMainGoal []

/-- Prove `c₁ ≡ᵤ c₂` from an alignment: a list of windows `(aᵢ, bᵢ)`, each
a pair of gate lists on the full register, in the order they occur. Each
window is decided on its own wires and placed back; every other move is a
checked commutation. -/
elab "circuit_windows " ws:term : tactic => withMainContext do
  let (n, ty, a, b) ← readGoal
  let circ := mkApp (mkConst ``Quantum.Circuit) n
  let listTy ← mkAppM ``List #[← mkAppM ``Prod #[circ, circ]]
  let wsE ← instantiateMVars (← elabTermEnsuringType ws (some listTy))
  let mut windows : Array Window := #[]
  for p in ← readList wsE do
    let p ← whnf p
    let_expr Prod.mk _ _ l r := p | throwError "expected a pair of circuits, got{indentExpr p}"
    let l ← readList l
    let r ← readList r
    windows := windows.push { left := l, right := r, proof := ← windowProof n ty l r }
  let proof ← alignWindows n ty windows 0 (← readList a) (← readList b)
  (← getMainGoal).assign proof
  replaceMainGoal []

end Quantum.Circuit.Tactic
