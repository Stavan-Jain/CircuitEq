/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Semantics

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

* import only `CircuitEq.Semantics`, `CircuitEq.Structural`,
  `CircuitEq.Support` and this file (plus Mathlib), never the rewriting,
  layer or tactic modules, so that the certificate module can import every
  checker without a cycle;
* `check` must be kernel-evaluable: structural recursion, `Bool`-valued
  functions rather than chains of `Decidable` instances, `Nat` bit
  operations for wire masks and `𝔽₂` rows, no `Finset.sum`, no
  well-founded recursion;
* export one `Checker n` (or `PhaseChecker n`, `ScalarChecker n`), the
  normal form if there is one as a `NormalForm n`, and treat everything
  else as implementation.

`Checker.orElse` combines checkers, and `NormalForm.toChecker` turns a
normal form into the checker that compares both sides' forms.
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
