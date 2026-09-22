/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Decide

/-!
# The checker interface

A *checker* is a computable decision on some fragment of circuits together
with a soundness theorem: `check a b = true → a ≡ᵤ b`. Completeness is not
part of the contract, and `false` means "not decided", never
"inequivalent". Every certified normal form or decision procedure (the
phase-polynomial normaliser, the Clifford tableau, the small-window
evaluator) is packaged as one of these, so that the certificate language
can invoke any of them as a step and its replay theorem needs nothing
beyond `Checker.sound`.

Rules for a module that provides a checker:

* import only `CircuitEq.Decide`, `CircuitEq.Structural`,
  `CircuitEq.Support` and this file (plus Mathlib), never the rewriting,
  layer or tactic modules, so that the certificate module can import every
  checker without a cycle;
* `check` must be kernel-evaluable: structural recursion, `Bool`-valued
  functions rather than chains of `Decidable` instances, `Nat` bit
  operations for wire masks and `𝔽₂` rows, no `Finset.sum`, no
  well-founded recursion;
* export one `Checker n` (or `PhaseChecker n`, `PhaseFinder n`,
  `ScalarChecker n`), the normal form if there is one as a `NormalForm n`,
  and treat everything else as implementation.

`Checker.orElse` combines checkers, and `NormalForm.toChecker` turns a
normal form into the checker that compares both sides' forms.

Up to a global phase there are two contracts. A `PhaseChecker` answers
`Bool` and proves `a ≡ₚ b`; a `PhaseFinder` answers with the exponent and
proves `a ≡ₚ[k] b`, which is what composes across the windows of a
certificate. `evalPhaseChecker` and `evalPhaseFinder` are the basis
evaluator in the two forms, and `Checker.toFinder` makes every exact
checker a finder.
-/

namespace Quantum.Circuit

variable {n : ℕ}

/-- A certified decision procedure for `≡ᵤ` on some fragment of circuits. -/
structure Checker (n : ℕ) where
  /-- The decision; `false` means "not decided", not "inequivalent". -/
  check : Circuit n → Circuit n → Bool
  /-- A `true` answer is a proof. -/
  sound : ∀ a b, check a b = true → a ≡ᵤ b

/-- A certified decision procedure for `≡ₚ` on some fragment. -/
structure PhaseChecker (n : ℕ) where
  /-- The decision; `false` means "not decided". -/
  check : Circuit n → Circuit n → Bool
  /-- A `true` answer is a proof of equivalence up to one of the eight
  phases. -/
  sound : ∀ a b, check a b = true → a ≡ₚ b

/-- A certified decision procedure for `≡ₛ` on some fragment. -/
structure ScalarChecker (n : ℕ) where
  /-- The decision; `false` means "not decided". -/
  check : Circuit n → Circuit n → Bool
  /-- A `true` answer is a proof of equivalence up to a unit scalar. -/
  sound : ∀ a b, check a b = true → a ≡ₛ b

/-- An exact checker is a phase checker. -/
def Checker.toPhase (C : Checker n) : PhaseChecker n :=
  ⟨C.check, fun a b h => (C.sound a b h).toUpToPhase⟩

/-- A phase checker is a scalar checker. -/
def PhaseChecker.toScalar (C : PhaseChecker n) : ScalarChecker n :=
  ⟨C.check, fun a b h => (C.sound a b h).toUpToScalar⟩

/-- Try the first checker, then the second. -/
def Checker.orElse (C D : Checker n) : Checker n where
  check a b := C.check a b || D.check a b
  sound a b h := by
    by_cases hc : C.check a b = true
    · exact C.sound a b hc
    · exact D.sound a b (by simpa [hc] using h)

/-- Syntactic equality: the trivial checker. -/
def syntacticChecker (n : ℕ) : Checker n where
  check a b := decide (a = b)
  sound a _ h := of_decide_eq_true h ▸ Equivalent.refl a

/-- The small-window oracle: decide on the computational basis. Its cost
is exponential in `n`; it is the leaf for windows of a few qubits, never
the plan for a whole circuit. -/
def evalChecker (n : ℕ) : Checker n where
  check a b := decide (a ≡ᵤ b)
  sound _ _ h := of_decide_eq_true h

/-- Try the first phase checker, then the second. -/
def PhaseChecker.orElse (C D : PhaseChecker n) : PhaseChecker n where
  check a b := C.check a b || D.check a b
  sound a b h := by
    by_cases hc : C.check a b = true
    · exact C.sound a b hc
    · exact D.sound a b (by simpa [hc] using h)

/-- The small-window oracle up to a global phase: decide on the
computational basis, under each of the eight phases. Same cost and same
place as `evalChecker`. -/
def evalPhaseChecker (n : ℕ) : PhaseChecker n where
  check a b := decide (a ≡ₚ b)
  sound _ _ h := of_decide_eq_true h

/-! ### Phase finders

A `PhaseChecker` says that *some* phase relates two circuits. A proof that
is assembled from several windows needs more, because the phases of the
windows multiply and the product has to be named: a `PhaseFinder` answers
with the exponent, `find a b = some k` proving `a ≡ₚ[k] b`. This is the
contract of a `window` step when a certificate is replayed up to a global
phase (`replayPhase` in `CircuitEq.Certificate`). Every exact checker is a
finder that only ever answers `0`. -/

/-- A certified procedure that names the global phase between two circuits
of some fragment. -/
structure PhaseFinder (n : ℕ) where
  /-- The exponent found: `some k` claims `a = ω ^ k · b` as operators;
  `none` means "not decided", not "inequivalent". -/
  find : Circuit n → Circuit n → Option (Fin 8)
  /-- A phase found is a proof. -/
  sound : ∀ a b k, find a b = some k → a ≡ₚ[k] b

/-- An exact checker finds the phase `ω ^ 0 = 1`, or nothing. -/
def Checker.toFinder (C : Checker n) : PhaseFinder n where
  find a b := if C.check a b then some 0 else none
  sound a b k h := by
    by_cases hc : C.check a b = true
    · obtain rfl : 0 = k := by simpa [hc] using h
      exact (C.sound a b hc).toWithPhase
    · simp [hc] at h

/-- A finder, with the phase forgotten, is a phase checker. -/
def PhaseFinder.toChecker (F : PhaseFinder n) : PhaseChecker n where
  check a b := (F.find a b).isSome
  sound a b h := by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
    exact (F.sound a b k hk).toUpToPhase

/-- Try the first finder, then the second. -/
def PhaseFinder.orElse (F G : PhaseFinder n) : PhaseFinder n where
  find a b :=
    match F.find a b with
    | some k => some k
    | none => G.find a b
  sound a b k h := by
    cases hF : F.find a b with
    | some j =>
      rw [hF] at h
      exact F.sound a b k (hF.trans h)
    | none =>
      rw [hF] at h
      exact G.sound a b k h

/-- The small-window oracle with the phase named: the first of the eight
phases under which the basis decision succeeds (`findPhase`). Its cost is
exponential in `n`, like `evalChecker`'s. -/
def evalPhaseFinder (n : ℕ) : PhaseFinder n where
  find := findPhase
  sound _ _ _ h := findPhase_sound h

/-- A certified normal form for a fragment: `nf` is `none` outside the
fragment, and equal forms are equivalent circuits. An optimiser
resynthesises from the form; the checker compares it. -/
structure NormalForm (n : ℕ) where
  /-- The type of normal forms. -/
  NF : Type
  /-- Forms are compared syntactically. -/
  [decEq : DecidableEq NF]
  /-- The normaliser; `none` outside the fragment. -/
  nf : Circuit n → Option NF
  /-- Equal forms are equivalent circuits. -/
  sound : ∀ a b x, nf a = some x → nf b = some x → a ≡ᵤ b

/-- The checker of a normal form: both sides normalise to the same form. -/
def NormalForm.toChecker (F : NormalForm n) : Checker n where
  check a b :=
    match F.nf a, F.nf b with
    | some x, some y => @decide (x = y) (F.decEq x y)
    | _, _ => false
  sound a b h := by
    revert h
    cases ha : F.nf a with
    | none => simp
    | some x =>
      cases hb : F.nf b with
      | none => simp
      | some y =>
        intro h
        have hxy : x = y := @of_decide_eq_true (x = y) (F.decEq x y) h
        subst hxy
        exact F.sound a b x ha hb

end Quantum.Circuit
