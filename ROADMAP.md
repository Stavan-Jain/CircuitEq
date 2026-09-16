# Roadmap — a ladder from toy identities to circuits no checker can reach

The target is proving equivalence of *useful* quantum circuits that current
automated equivalence checkers cannot handle. This document breaks that into
rungs of increasing difficulty. Each rung has a concrete acceptance test, so
progress is measurable, and each leaves reusable library behind, so the rungs
above it get cheaper. They are ordered by difficulty and dependency; they need
not be finished strictly in sequence.

## Where the bar is

Automated equivalence checkers — decision diagrams (QCEC in the Munich Quantum
Toolkit), ZX-calculus rewriting (PyZX), path sums (Feynman), SAT and weighted
model counting, and the newer checkers that the
[QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits)
benchmark targets — share three limits.

1. **Fixed qubit count.** A statement about a family for all `n` cannot be
   expressed, let alone decided.
2. **One technique per tool.** A pair that defeats the technique — two
   structurally different implementations, a T-heavy circuit that blows up a
   decision diagram, a rewriting strategy that does not terminate — yields
   "unknown", not "no".
3. **No certificate.** A "yes" is the tool's word. Nothing independently
   checkable is produced.

Proof assistants (SQIR/VOQC in Coq, QBricks over Why3, CoqQ, Isabelle) have
none of these limits, but their proofs are hand-written, and the existing work
verifies compiler *passes* or algorithm *correctness* rather than equivalence
of arbitrary circuit pairs on demand.

**Beyond state of the art** therefore means one of three things. Every rung
says which it delivers.

- **P (parametric).** The theorem quantifies over the qubit count `n` or over
  gate parameters `θ`. No fixed-size checker can state it.
- **S (scale).** A fixed-`n` instance on which QCEC, PyZX and Feynman all fail
  within one hour on a workstation, and our proof checks.
- **T (trust).** An instance a checker handles, but the result is a
  kernel-checked proof depending on three standard axioms rather than a tool's
  output.

P is the headline. T comes almost for free from the design. S must be measured,
not claimed; the benchmark protocol at the end is part of the roadmap.

## The ladder

### Rung 0 — Prototype ✅ (September 2026)

Computable ℚ(ζ₈); sparse state-vector semantics; `≡ᵤ` and `≡ₚ` decidable for
concrete circuits; a structural toolkit; twenty identities, several parametric
in `n` (`hLayer_hLayer`, `T_cnot_comm`, `H_T_H_eq_T`).

Limits: the gate alphabet is single-qubit Clifford+T plus CNOT; concrete
checks cost `2^depth`; there is no link to ℂ; no ancilla-aware equivalence.

### Rung 1 — Concrete circuits at benchmark scale

**Goal.** Decide `≡ᵤ` for concrete Clifford+T circuits of the size real
benchmarks have: 10–12 qubits, depth in the hundreds to low thousands.

**Work.** A materialised evaluator over `List`/`Array`, gate by gate, so cost
is `O(depth · 2^n)` instead of `O(2^depth)`; the theorem that it agrees with
`denote`; a `Decidable` instance routed through it. If ℚ's gcd normalisation
dominates, re-represent `Zeta8` as ℤ numerators over a shared power of √2 (the
exact-synthesis ring `D[ω]`). Packed `Nat` bit-vectors where lists are too slow
for the kernel — the technique that de-nativised QECLean's gross-code proof.

**Acceptance.** Verify all 19 origin circuits of QECUnitaryCircuits against
their PyZX-optimised twins, and refute their gate-deleted mutants, each in
under one minute of kernel time. Publish the scaling table (n, depth, seconds).

**Delivers.** T. **Harder because** the evaluator correspondence is the
library's first genuine reflection proof, and kernel performance engineering is
unforgiving.

### Rung 2 — A trusted specification

**Goal.** Make "the denotation is the unitary you meant" defensible, so every
theorem above means what it says.

**Work.** OpenQASM 2/3 ingestion by a generator that emits `Circuit n` terms
(never hand-edited); differential testing of `denote` against a numpy
statevector simulator on ten thousand random circuits, which catches
endianness, control/target and phase-convention errors; `Zeta8.toComplex :
Zeta8 →+* ℂ` with `ω ↦ exp(iπ/4)`; unitarity of every `Gate1.mat`; agreement
of the mapped matrices with QECLean's `QEC/Foundations` gates.

**Acceptance.** The random-circuit diff is zero; every gate is proved unitary;
the bridge lemmas to QECLean compile.

**Delivers.** T, the trust half. **Harder because** the ℂ side is
noncomputable, so these are analytic proofs about `Complex.exp`, not `decide`.

### Rung 3 — Equivalence notions compilers actually need

**Goal.** State the equivalences that arise from compilation and from
ancilla-using constructions.

**Work.** Equivalence up to a qubit permutation (routing, SWAP insertion);
equivalence on the ancilla subspace (the last `a` qubits enter and leave in
`|0⟩`); equivalence up to a relative phase on a subspace (Margolus-style
relative-phase Toffolis). Congruence lemmas for each under sequencing, and
decidability wherever the quantifier is finite.

**Acceptance.** Qiskit-transpiled versions of the 19 benchmark circuits, with
SWAPs and layout changes, verified against their sources; the 4-T
relative-phase Toffoli verified against Toffoli under the right relation.

**Delivers.** T, plus the prerequisites for every P result about ancilla-using
constructions. **Harder because** the definitions are subtle — which side a
permutation acts on, what "restored ancilla" means on superposed inputs — and a
wrong one silently weakens everything built on it.

### Rung 4 — A complete, certified Clifford decision procedure

**Goal.** Decide equivalence of Clifford circuits at hundreds to thousands of
qubits, with a witness on failure.

**Work.** Tableau semantics: a Clifford circuit maps to a symplectic matrix over
`𝔽₂` plus a sign vector. The theorem that the tableau determines the unitary up
to phase (Paulis span the matrix algebra, so the commutant is scalar);
completeness (equal tableaux imply `≡ₚ`); a Pauli witness `P` with
`U₁ P U₁† ≠ U₂ P U₂†` on refutation; kernel evaluation in `ZMod 2` packed as
`Nat` bit rows; hooks into QECLean's binary-symplectic layer. Generic `k`-qubit
gate placement `applyGate G qs` on the way.

**Acceptance.** GHZ/cat-state ladders and stabilizer-state preparation
circuits for QECLean's codes at `n ≥ 100` verified in seconds; a wrong pair
yields a concrete Pauli.

**Delivers.** T, and S relative to every non-tableau checker. **Harder
because** the soundness theorem is real linear algebra over ℚ(ζ₈), and the
procedure has to be fast in the kernel, not merely correct.

### Rung 5 — The classical reversible layer: adders and multi-controlled gates for all `n`

**Goal.** The first useful parametric theorems.

**Work.** A predicate for circuits of `X`, `CNOT` and Toffoli, with Toffoli a
macro for its 15-gate Clifford+T decomposition verified once at `n = 3` and
lifted by a placement lemma; the theorem that such a circuit permutes basis
states by a Boolean function built compositionally; `≡ᵤ` on classical circuits
reduced to equality of Boolean functions; induction principles for ripple
structures.

**Acceptance.**
`∀ n, cuccaroAdder n ≡ vbeAdder n` (Cuccaro 2004 against Vedral–Barenco–Ekert
1996, up to layout permutation); `∀ n, barencoCnX n ≡ᵃ cnX n` (multi-controlled
`X` via Toffolis with ancilla against its specification, ancilla-aware);
`∀ n, cnotLadder n ≡ᵤ [CX 0 n]`. Fixed-`n` instances run through the benchmark
protocol for the crossover table.

**Delivers.** P, the first time. Probably S at `n ≈ 32–64`, where the T-count
reaches the hundreds. **Harder because** the proofs are inductions with
carry-chain invariants: the first place an agent must do mathematics rather
than evaluation.

### Rung 6 — Agent milestone A: reproduce, then extend

**Goal.** Establish that an agent can drive the library.

**Work.** A harness that gives an agent (Claude, Aristotle, or similar) a
statement, the library and the lean-lsp tools, and records outcome, time and
tokens; a held-out set of the existing parametric theorems with proofs removed.

**Acceptance.** At least 80 % of the Rung 0–5 parametric theorems re-proved
unaided from statements; at least one new parametric identity found and proved
that no human wrote; a written account of every failure mode observed.

**Delivers.** The evidence for the project's central bet. **Harder because**
success is, for the first time, not under our control.

### Rung 7 — Dyadic rotations and the Fourier layer: QFT and the QFT adder for all `n`

**Goal.** Leave Clifford+T. The QFT needs rotations by `2π/2^k` for `k` up to
`n`, so the coefficient field grows with `n`.

**Work.** Gates `Rz(k) = diag(1, ζ_{2^k})` and their controlled versions;
coefficients either in a tower `ℚ(ζ_{2^m})` or, better, as phase polynomials
with exponents in `ZMod (2^m)`; a certified normaliser for the CNOT + diagonal
fragment, where equivalence is exactly equality of a linear reversible map plus
a phase polynomial, so that fragment gets a *complete* procedure; the Fourier
lemma that the QFT diagonalises addition.

**Acceptance.** `∀ n, qft n ≡ᵤ qftSpec n` (recursive circuit against the DFT
matrix); `∀ n, qft n ++ qftInv n ≡ᵤ []`; `∀ n, draperAdder n ≡ cuccaroAdder n`,
a proof that crosses the Fourier and classical layers.

**Delivers.** P and S. **Harder because** the coefficient ring is no longer
fixed, and the key lemma is a piece of mathematics, not a rewrite.

### Rung 8 — Symbolic parameters: gate-set translations and Trotter steps for all `θ`

**Goal.** Equivalences that hold for every value of a continuous parameter.

**Work.** `Rz(θ)` with `θ` a formal variable; semantics over Laurent
polynomials in `e^{iθ/2}`, or over a general commutative ring with a
distinguished unit; equivalence for all `θ` as a polynomial identity closed by
`ring`; joint families in `n` and `θ`.

**Acceptance.** A standard compiler's gate equivalence library — Qiskit's has
roughly a hundred rules such as `rzz(θ) = cx; rz(θ); cx` and the
controlled-rotation decompositions — verified for all `θ`; the standard
`exp(−iθ Z⊗Z)` implementations; a parametrised ansatz layer for all `n` and `θ`.

**Delivers.** P in `θ`. Quartz verifies fixed rules by SMT, so the single-rule
case is matched; the joint `n`-and-`θ` families are new. **Harder because**
normal forms for trigonometric identities need care to stay decidable.

### Rung 9 — QEC circuits on the code subspace, with QECLean

**Goal.** The project's home turf: encoders, transversal gates and syndrome
extraction as unitary equivalences on a code space.

**Work.** Import stabilizer codes from QECLean; define "implements the logical
gate" and "equivalent modulo the stabilizer group" as circuit-level relations;
apply the classical layer from Rung 5 to CNOT syndrome-extraction schedules;
use QECLean's parametric toric and rotated-surface families for statements in
the lattice size `L`.

**Acceptance.** Every transversal-gate circuit in QECUnitaryCircuits proved as
a logical-gate theorem: Steane `H`, `S`, `CNOT`, and `[[15,1,3]]` transversal
`T` as logical `T`; the Chamberland–Cross flag circuit equivalent on the code
space to its non-fault-tolerant version; `∀ L`, the toric-code
syndrome-extraction schedule maps code states with `|0⟩` ancillas to code
states carrying the syndromes.

**Delivers.** P and T in a domain where no checker has the vocabulary.
**Harder because** the relations are subspace-relative and the codes are
parametric; Rungs 3, 4 and 5 are all load-bearing.

### Rung 10 — Agent milestone B, and the benchmark

**Goal.** An unaided beyond-SOTA theorem, and an honest public comparison.

**Work.** The agent proves a new Rung 7 or Rung 9 theorem given only the
statement and the library; the benchmark protocol is run in full and published
with the crossover table; a write-up of the method.

**Acceptance.** One theorem of type P proved end to end by the agent and
merged; the crossover table shows at least one family of type S.

### Rung 11 — Summit: arithmetic for Shor, for all `n`

**Goal.** A theorem whose fixed-`n` instances have thousands of qubits and
millions of gates.

**Work.** Controlled modular multiplication as in Beauregard (QFT-based)
against a Toffoli-based implementation, equivalent for all `n`; components of
windowed arithmetic in the Gidney–Ekerå style. Rungs 5, 7 and 8 combine here.

**Acceptance.** `∀ n, modMulBeauregard n a N ≡ modMulToffoli n a N` on the
relevant subspace, with `a` and `N` symbolic where the mathematics allows.

**Delivers.** P at a scale where S is automatic: no checker can state or
approach it.

## Benchmark protocol (how S is measured)

For each family with fixed-`n` instances: run QCEC (`mqt.qcec`), PyZX
(`full_reduce` on `U†V`, and `compare_tensors` where feasible), Feynman
(`feynver`), and any newer checker such as the one QECUnitaryCircuits targets,
with a one-hour timeout and 16 GB, at `n = 4, 8, 16, 32, 64, 128`. Record
pass, fail or timeout, and time. Our result covers all `n` by one proof; report
the smallest `n` at which each tool fails as the crossover. Report honestly that
on compilation-flow pairs, where the two circuits are structurally close,
decision-diagram tools will beat kernel checking at every `n`; the advantage
there is T, not S.

## Cross-cutting tracks

- **Performance.** Reflection, packed `Nat`, no `Finset.sum` in anything the
  kernel evaluates; measured on every rung.
- **Trust.** The axiom policy in CI; differential testing against a simulator;
  the ℂ bridge. Nothing here uses `native_decide`.
- **Flywheel.** Every proved equivalence is a lemma. Keep `Structural.lean`
  curated, grow a `simp` set, and record which lemmas agents actually reach for.
- **Documentation.** Each rung lands with a short design note.

## Dependencies

Rung 1 before 4 and 5. Rung 2 alongside 1. Rung 3 before 5 and 9. Rung 4
before 9. Rung 5 before 7, and 7 before 11. Rung 8 before 11. Rung 6 after 5.
Rung 10 after 7 or 9.

## Risks and fallbacks

- **Kernel performance wall.** Fallback: a clearly labelled second trust tier
  using `native_decide` for concrete checks only, never for library lemmas.
- **A parametric target needs new mathematics.** That is the point; scope the
  acceptance test to what is provable and record the rest as conjectures.
- **Coefficient-field growth in Rung 7.** Prefer phase polynomials to a tower
  of fields.
- **Agent reliability.** The library and decision procedures have standalone
  value; the agent rungs are evidence, not prerequisites.
- **Specification drift.** Rung 2 is not optional.

## Suggested order for the next quarter

Rung 1, then 2, then 3, then 5, then 6. Take Rung 4 only if Clifford circuits
become the bottleneck. Rung 5 is the first result worth writing up.
