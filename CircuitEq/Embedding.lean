/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Relations
import Mathlib.Logic.Function.Basic
import Init.Data.BitVec.Lemmas

/-! # Placing a circuit on selected wires: the locality theorem

An injective map of wire indices `f : Fin m ↪ Fin n` places an `m`-qubit
circuit on `m` wires of an `n`-qubit register (`rename f`), and
`rename_equivalent_iff` says this preserves and reflects `≡ᵤ`. So an identity
decided by the kernel on `m` qubits, at cost `2 ^ m`, holds on any `m`
distinct wires of any register (`Equivalent.rename`), and a window of a big
circuit that touches only `m` wires can be checked on `m` qubits.

The same holds up to a global phase, with the phase kept:
`rename_equivalentWithPhase_iff` for `≡ₚ[k]`, `rename_equivalentUpToPhase_iff`
for `≡ₚ`, and `EquivalentWithPhase.rename` / `EquivalentUpToPhase.rename`
to place an identity; `EquivalentUpToScalar.rename` places one up to a unit
scalar.

The proof slices an arbitrary large-register vector by fixing the unused
bits. Only the proof's indexing helpers are noncomputable; circuit placement
is a computable map of instructions, and `simp` evaluates it.
-/

namespace Quantum.Circuit

variable {m n : ℕ}

/-- Assemble a computational-basis index from its little-endian bits. -/
def packBits (f : Fin n → Bool) : Fin (2 ^ n) :=
  ((BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)).toFin

/-- Reading an assembled bit recovers the supplied Boolean. -/
@[simp] theorem bit_packBits (f : Fin n → Bool) (i : Fin n) : bit i (packBits f) = f i := by
  change (((BitVec.ofBoolListLE (List.ofFn f)).cast _).getLsbD i.val) = _
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, dif_pos i.isLt]
  rfl

/-- Computational-basis indices are determined by their in-range bits. -/
theorem basisIndex_ext {x y : Fin (2 ^ n)} (h : ∀ i : Fin n, bit i x = bit i y) : x = y := by
  have hb : BitVec.ofFin x = BitVec.ofFin y :=
    BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i, hi⟩)
  exact congrArg BitVec.toFin hb

/-- Read the selected wires of a larger basis index. -/
def restrictBits (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ m) :=
  packBits fun i => bit (f i) x

/-- Set selected wires to a small index, retaining all other bits. -/
noncomputable def patchBits (f : Fin m ↪ Fin n) (x : Fin (2 ^ n))
    (y : Fin (2 ^ m)) : Fin (2 ^ n) :=
  packBits (Function.extend f (fun i => bit i y) (fun j => bit j x))

/-- Patching sets each selected bit to its corresponding small-register bit. -/
@[simp] theorem bit_patchBits (f : Fin m ↪ Fin n) (x : Fin (2 ^ n))
    (y : Fin (2 ^ m)) (i : Fin m) : bit (f i) (patchBits f x y) = bit i y := by
  simp [patchBits, f.injective.extend_apply]

/-- Patching leaves every unselected bit unchanged. -/
theorem bit_patchBits_other (f : Fin m ↪ Fin n) (x : Fin (2 ^ n))
    (y : Fin (2 ^ m)) (j : Fin n) (hj : ¬ ∃ i, f i = j) :
    bit j (patchBits f x y) = bit j x := by
  simp [patchBits, Function.extend_apply' _ _ _ hj]

/-- Restriction recovers every bit supplied to a patch. -/
@[simp] theorem restrict_patch (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) (y : Fin (2 ^ m)) :
    restrictBits f (patchBits f x y) = y := by
  apply basisIndex_ext
  intro i
  simp [restrictBits]

/-- Patching an index with its own selected bits preserves the index. -/
@[simp] theorem patch_restrict (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) :
    patchBits f x (restrictBits f x) = x := by
  apply basisIndex_ext
  intro j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [restrictBits]
  · exact bit_patchBits_other f x _ j hj

/-- Flipping a selected bit commutes with placing the small register. -/
theorem patch_flipBit (f : Fin m ↪ Fin n) (x : Fin (2 ^ n))
    (y : Fin (2 ^ m)) (i : Fin m) :
    patchBits f x (flipBit i y) = flipBit (f i) (patchBits f x y) := by
  apply basisIndex_ext
  intro j
  by_cases hj : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := hj
    by_cases hki : k = i
    · subst k; simp
    · simp [bit_flipBit_of_ne hki, bit_flipBit_of_ne (f.injective.ne hki)]
  · have hji : j ≠ f i := fun h => hj ⟨i, h.symm⟩
    rw [bit_patchBits_other f x _ j hj, bit_flipBit_of_ne hji,
      bit_patchBits_other f x _ j hj]

/-- Place an instruction on the selected wires of another register. -/
def Instr.rename (f : Fin m ↪ Fin n) : Instr m → Instr n
  | .one g i => .one g (f i)
  | .cnot c t => .cnot (f c) (f t)

@[simp] lemma Instr.rename_one (f : Fin m ↪ Fin n) (g : Gate1) (i : Fin m) :
    (Instr.one g i).rename f = Instr.one g (f i) := rfl

@[simp] lemma Instr.rename_cnot (f : Fin m ↪ Fin n) (c t : Fin m) :
    (Instr.cnot c t).rename f = Instr.cnot (f c) (f t) := rfl

/-- Place a circuit on selected wires, preserving instruction order. -/
def rename (f : Fin m ↪ Fin n) (c : Circuit m) : Circuit n := c.map (Instr.rename f)

@[simp] lemma rename_nil (f : Fin m ↪ Fin n) : rename f [] = [] := rfl

@[simp] lemma rename_cons (f : Fin m ↪ Fin n) (g : Instr m) (c : Circuit m) :
    rename f (g :: c) = g.rename f :: rename f c := rfl

/-- The embedding of a one-qubit register on a wire. -/
def wires₁ (i : Fin n) : Fin 1 ↪ Fin n :=
  ⟨![i], Function.injective_of_subsingleton _⟩

/-- The embedding of a two-qubit register on two distinct wires. -/
def wires₂ {i j : Fin n} (h : i ≠ j) : Fin 2 ↪ Fin n :=
  ⟨![i, j], by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- The embedding of a three-qubit register on three distinct wires. -/
def wires₃ {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ Fin n :=
  ⟨![a, b, c], by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all⟩

/-- The embedding given by a duplicate-free list of wires: qubit `i` of the
small register is the `i`-th listed wire. This is the embedding the window
tactic builds. -/
def wiresOf (l : List (Fin n)) (h : l.Nodup) : Fin l.length ↪ Fin n :=
  ⟨l.get, List.nodup_iff_injective_get.mp h⟩

@[simp] lemma wiresOf_apply (l : List (Fin n)) (h : l.Nodup) (i : Fin l.length) :
    wiresOf l h i = l.get i := rfl

/-- Slice a large-register state by fixing its unselected bits. -/
noncomputable def slice (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) (ψ : Vec n) : Vec m :=
  fun y => ψ (patchBits f x y)

/-- Instruction action agrees on every slice of the larger register. -/
theorem slice_apply (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) (g : Instr m) (ψ : Vec n) :
    slice f x ((g.rename f).apply ψ) = g.apply (slice f x ψ) := by
  funext y
  cases g <;> simp [slice, Instr.rename, Instr.apply, applyOne, applyCNOT, patch_flipBit]

/-- A placed circuit acts on each slice exactly as the small circuit. -/
theorem slice_denote (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) (c : Circuit m) (ψ : Vec n) :
    slice f x (denote (rename f c) ψ) = denote c (slice f x ψ) := by
  induction c generalizing ψ with
  | nil => rfl
  | cons g c ih => simpa [rename, slice_apply] using ih ((g.rename f).apply ψ)

/-- Any proved identity can be placed on arbitrary distinct wires. -/
theorem Equivalent.rename {a b : Circuit m} (h : a ≡ᵤ b) (f : Fin m ↪ Fin n) :
    rename f a ≡ᵤ rename f b := by
  intro ψ
  funext x
  have hs := h (slice f x ψ)
  rw [← slice_denote f x a ψ, ← slice_denote f x b ψ] at hs
  have hx := congrFun hs (restrictBits f x)
  simpa [slice] using hx

/-- Transfer an identity on `k` qubits to its placement on `k` wires of a
larger register, with the placed circuits given up to definitional
unfolding. This is the form the window tactic produces: `h` is decided on
`k` qubits, and the two equations are `rfl`. -/
theorem Equivalent.of_rename {k : ℕ} (f : Fin k ↪ Fin n) {a' b' : Circuit k}
    {a b : Circuit n} (h : a' ≡ᵤ b') (ha : Quantum.Circuit.rename f a' = a)
    (hb : Quantum.Circuit.rename f b' = b) : a ≡ᵤ b := by
  subst ha hb
  exact h.rename f

/-- Equivalence on selected wires is equivalent to the smaller problem. -/
theorem rename_equivalent_iff (f : Fin m ↪ Fin n) (a b : Circuit m) :
    rename f a ≡ᵤ rename f b ↔ a ≡ᵤ b := by
  refine ⟨?_, fun h => h.rename f⟩
  intro h ψ
  have hψ : slice f 0 (fun x => ψ (restrictBits f x)) = ψ := by
    funext y
    simp [slice]
  have hs := congrArg (slice f 0) (h (fun x => ψ (restrictBits f x)))
  rwa [slice_denote, slice_denote, hψ] at hs

/-! ### Locality up to a scalar

The slicing argument does not care what relates the two small circuits: if
`a` is `s` times `b` as operators, for any scalar `s`, then so are their
placements, and conversely. With `s = ω ^ k` this is the locality theorem
for a named phase, from which the one for `≡ₚ` follows, so a window that
holds only up to a global phase is still decided on its own wires, at cost
`2 ^ m`, and its phase is the phase it contributes to the whole circuit.
With a unit `s` it is the placement lemma for `≡ₛ`. -/

/-- Slicing commutes with scaling. -/
lemma slice_smul (f : Fin m ↪ Fin n) (x : Fin (2 ^ n)) (s : Zeta8) (ψ : Vec n) :
    slice f x (s • ψ) = s • slice f x ψ := rfl

/-- Placement preserves a scalar relation between two circuits. -/
lemma denote_rename_eq_smul {a b : Circuit m} {s : Zeta8}
    (h : ∀ ψ, denote a ψ = s • denote b ψ) (f : Fin m ↪ Fin n) (ψ : Vec n) :
    denote (rename f a) ψ = s • denote (rename f b) ψ := by
  funext x
  have hs := h (slice f x ψ)
  rw [← slice_denote f x a ψ, ← slice_denote f x b ψ] at hs
  have hx := congrFun hs (restrictBits f x)
  simpa [slice] using hx

/-- Placement reflects a scalar relation between two circuits. -/
lemma denote_eq_smul_of_rename {a b : Circuit m} {s : Zeta8} (f : Fin m ↪ Fin n)
    (h : ∀ ψ, denote (rename f a) ψ = s • denote (rename f b) ψ) (ψ : Vec m) :
    denote a ψ = s • denote b ψ := by
  have hψ : slice f 0 (fun x => ψ (restrictBits f x)) = ψ := by
    funext y
    simp [slice]
  have hs := congrArg (slice f 0) (h (fun x => ψ (restrictBits f x)))
  rwa [slice_smul, slice_denote, slice_denote, hψ] at hs

/-- Any identity with a named phase can be placed on arbitrary distinct
wires, and keeps its phase. -/
theorem EquivalentWithPhase.rename {k : Fin 8} {a b : Circuit m} (h : a ≡ₚ[k] b)
    (f : Fin m ↪ Fin n) : rename f a ≡ₚ[k] rename f b :=
  denote_rename_eq_smul h f

/-- Transfer an identity with a named phase on `m` qubits to its placement
on `m` wires of a larger register, with the placed circuits given up to
definitional unfolding; the phase form of `Equivalent.of_rename`. -/
theorem EquivalentWithPhase.of_rename {k : Fin 8} (f : Fin m ↪ Fin n)
    {a' b' : Circuit m} {a b : Circuit n} (h : a' ≡ₚ[k] b')
    (ha : Quantum.Circuit.rename f a' = a) (hb : Quantum.Circuit.rename f b' = b) :
    a ≡ₚ[k] b := by
  subst ha hb
  exact h.rename f

/-- The locality theorem with a named phase: on selected wires the phase is
the phase of the smaller problem. -/
theorem rename_equivalentWithPhase_iff (f : Fin m ↪ Fin n) (k : Fin 8) (a b : Circuit m) :
    rename f a ≡ₚ[k] rename f b ↔ a ≡ₚ[k] b :=
  ⟨fun h => denote_eq_smul_of_rename f h, fun h => h.rename f⟩

/-- Any identity up to a global phase can be placed on arbitrary distinct
wires. -/
theorem EquivalentUpToPhase.rename {a b : Circuit m} (h : a ≡ₚ b) (f : Fin m ↪ Fin n) :
    rename f a ≡ₚ rename f b := by
  obtain ⟨k, (hk : a ≡ₚ[k] b)⟩ := h
  exact ⟨k, hk.rename f⟩

/-- Transfer an identity up to a global phase on `m` qubits to its placement
on `m` wires of a larger register; the phase form of
`Equivalent.of_rename`. -/
theorem EquivalentUpToPhase.of_rename (f : Fin m ↪ Fin n) {a' b' : Circuit m}
    {a b : Circuit n} (h : a' ≡ₚ b') (ha : Quantum.Circuit.rename f a' = a)
    (hb : Quantum.Circuit.rename f b' = b) : a ≡ₚ b := by
  subst ha hb
  exact h.rename f

/-- The locality theorem up to a global phase: equivalence up to phase on
selected wires is equivalent to the smaller problem. -/
theorem rename_equivalentUpToPhase_iff (f : Fin m ↪ Fin n) (a b : Circuit m) :
    rename f a ≡ₚ rename f b ↔ a ≡ₚ b :=
  exists_congr fun k => rename_equivalentWithPhase_iff f k a b

/-- Any identity up to a unit scalar can be placed on arbitrary distinct
wires. -/
theorem EquivalentUpToScalar.rename {a b : Circuit m} (h : a ≡ₛ b) (f : Fin m ↪ Fin n) :
    rename f a ≡ₛ rename f b := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, denote_rename_eq_smul h f⟩

end Quantum.Circuit
