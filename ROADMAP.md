# Roadmap — a ladder from toy identities to circuits no checker can reach

The target is proving equivalence of *useful, real-world* quantum circuits
that current automated equivalence checkers cannot handle. This document
breaks that into rungs of increasing difficulty. Each rung has a concrete
acceptance test, so progress is measurable, and each leaves reusable library
behind, so the rungs above it get cheaper. They are ordered by difficulty and
dependency; they need not be finished strictly in sequence.

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

## Goal, method, byproduct

A result can go beyond the state of the art in three ways. They are not
equally important, and every rung below says which it delivers.

- **S — scale. The goal.** A fixed-size, real-world circuit pair on which
  QCEC, PyZX and Feynman all fail within one hour on a workstation, and our
  proof checks. This is what a practitioner holding two compiled circuits
  needs, and it is the measure of success for the project.
- **P — parametric. The method.** A theorem quantified over the qubit count
  `n` or over gate parameters `θ`. Real circuits are instances of templates
  (adders, QFTs, multi-controlled gates, Trotter steps, syndrome-extraction
  rounds), and for a template-shaped instance the only known way to beat the
  exponential is to exploit that structure, which is a parametric argument
  whether or not the `∀ n` is written down: the induction hypothesis needs the
  general form. A proof for all `n` instantiated at `n = 64` is an S result at
  zero marginal cost, and a library of proved templates verifies real
  instances by matching and instantiation rather than by paying for a proof
  each time.
- **T — trust. The byproduct.** A kernel-checked proof on three standard
  axioms rather than a tool's output. It comes free from the design. It
  matters in certification settings and because a proved lemma composes into
  larger proofs, which a tool's "yes" cannot, but it is not a goal in itself.

### What "structure" means for compiled circuits

This is the project's working hypothesis. Rung 4 is its test.

Exact equivalence is coNP-hard, so in the worst case every method fails at
about the same size, ours included. But circuits that come out of compilers
and optimisers are never worst-case. A peephole or resynthesis pass relates
its output to its input by a chain of local, sound rewrites. The original
template may be gone, but the *relation* between the two circuits is still
highly structured, and that relation is what a proof exploits. An agent free
to choose the decomposition can find it where a fixed-strategy tool cannot.
Reach on fixed-size pairs is therefore bounded by whether a decomposition
exists, not by whether the circuit looks structured, and for optimiser output
one almost always exists because the optimiser created it. The genuinely
adversarial cases — random circuits, or a circuit re-synthesised from its
unitary matrix so that no rewrite path survives — have no such relation, and
they are not real-world inputs.

Three mechanisms, and the proof shapes they become in this library:

- **Aligned windows.** Local optimisation changes circuits locally, so the two
  circuits split into aligned windows, each pair equivalent as a small
  unitary on the few qubits it touches. The proof is many tiny `decide`s glued
  by `Equivalent.append`, with the moving lemmas inserting the commutations
  that let a gate cross a window boundary. Cost is linear in circuit size and
  independent of `n`, given the locality theorem of Rung 4. Finding the
  alignment is the creative step; QCEC's alternating scheme does it by a fixed
  heuristic, and that is exactly the freedom an agent adds.
- **Residual invariants.** At agent-chosen cut points, assert that one
  circuit's prefix times the inverse of the other's is something compact — a
  Clifford, a diagonal — and prove each step preserves it. This is a loop
  invariant; tools cannot invent them, agents and humans do routinely. The
  tableau layer of Rung 5 is what represents a Clifford residual compactly.
- **Latent algebra.** Between Hadamard layers every Clifford+T circuit is a
  CNOT-plus-diagonal fragment with a canonical phase-polynomial form. An agent
  can reason in that form across the Hadamard boundaries, case by case, where
  a fixed reduction system stalls. The normaliser of Rung 8 is the tool.

## The ladder

### Rung 0 — Prototype ✅ (September 2026)

Computable ℚ(ζ₈); sparse state-vector semantics; `≡ᵤ` and `≡ₚ` decidable for
concrete circuits; a structural toolkit; twenty identities, several parametric
in `n` (`hLayer_hLayer`, `T_cnot_comm`, `H_T_H_eq_T`).

Limits: the gate alphabet is single-qubit Clifford+T plus CNOT; concrete
checks cost `2^depth`; there is no link to ℂ; no ancilla-aware equivalence; no
locality theorem, so every `decide` pays for all `n` qubits.

### Rung 1 — Concrete circuits at benchmark scale

**Goal.** Decide `≡ᵤ` for concrete Clifford+T circuits of the size real
benchmarks have: 10–12 qubits, depth in the hundreds to low thousands.

**Work.** A materialised evaluator over `List`/`Array`, gate by gate, so cost
is `O(depth · 2^n)` instead of `O(2^depth)`; a *proof* that it agrees with
`denote` (its correctness is a theorem, not a test); a `Decidable` instance
routed through it. If ℚ's gcd normalisation dominates, re-represent `Zeta8` as
ℤ numerators over a shared power of √2 (the exact-synthesis ring `D[ω]`).
Packed `Nat` bit-vectors where lists are too slow for the kernel — the
technique that de-nativised QECLean's gross-code proof.

**Acceptance.** Verify all 19 origin circuits of QECUnitaryCircuits against
their PyZX-optimised twins, and refute their gate-deleted mutants, each in
under one minute of kernel time. Publish the scaling table (n, depth, seconds).

**Delivers.** The brute-force baseline for S, and T. **Harder because** the
evaluator correspondence is the library's first reflection proof, and kernel
performance engineering is unforgiving.

### Rung 2 — A trusted specification

**Goal.** Make "the denotation is the unitary you meant" defensible with the
least machinery that actually catches errors.

**Work.** Three layers, treated differently.

- *The semantics* — `Gate1.mat`, `applyOne`, `applyCNOT`, `bit`, `flipBit`,
  `denote` — are small enough to review by hand, and the identity lemmas
  (`H_mul_H`, `T_mul_T`, `cnot_cnot`, …) already pin down most conventions.
  Review, document the conventions (little-endian bits, control first, time
  order), and stop there.
- *The fast evaluator* of Rung 1 is proved equal to `denote`. No testing.
- *The QASM generator* is code outside Lean with no proof, and the place
  convention errors actually live. It gets a conformance check against Qiskit:
  the benchmark files plus a few hundred random circuits, statevectors
  compared, run in CI. The motivating trap: Qiskit's `rz(θ)` is
  `e^{−iθ/2} · p(θ)`, so a generator that maps `rz(π/4)` to `T` makes `≡ᵤ`
  false whenever the two sides contain different numbers of `rz` gates,
  while every identity lemma still holds.

Also `Zeta8.toComplex : Zeta8 →+* ℂ` with `ω ↦ exp(iπ/4)`; unitarity of every
`Gate1.mat`; agreement of the mapped matrices with QECLean's `QEC/Foundations`
gates.

**Acceptance.** The conformance check reports zero mismatches; every gate is
proved unitary; the bridge lemmas to QECLean compile.

**Delivers.** T. **Harder because** the ℂ side is noncomputable, so those are
analytic proofs about `Complex.exp`, not `decide`.

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

**Delivers.** T, plus the prerequisites for Rungs 4 and 6. **Harder because**
the definitions are subtle — which side a permutation acts on, what "restored
ancilla" means on superposed inputs — and a wrong one silently weakens
everything built on it.

### Rung 4 — Compositional proofs of fixed-size pairs

**Goal.** The direct route to S on real compiled circuits, and the empirical
test of the working hypothesis above.

**Work.**

- **The locality theorem.** If two sub-circuits touch only a set of `k`
  qubits, their equivalence on `n` qubits is equivalent to the equivalence of
  their restrictions on `k` qubits. This needs generic gate placement and a
  restriction map, and it is what makes a window cost `2^k` instead of `2^n`.
  It is the single most valuable lemma not yet in the library and should be
  the first thing built at this rung.
- **The window pattern.** Given an alignment — a matching of windows between
  the two circuits, plus the commutations needed to make them adjacent — a
  tactic or macro discharges the whole equivalence by congruence, moving
  lemmas, and one small `decide` per window. The alignment is *input*; the
  tactic only checks it.
- **The residual pattern.** Cut points with a compact residual (diagonal
  first; Clifford once Rung 5 lands), proved preserved step by step.
- **The optimiser-output benchmark.** For each of the 19 QECUnitaryCircuits
  origins, and for adders and QFTs at `n = 8` to `64`: the output of PyZX
  `full_reduce` plus extraction, of a T-count optimiser (quizx, or Feynman's
  optimiser), and of Qiskit at optimisation level 3. These pairs are
  structurally different and T-heavy, which is where decision-diagram tools
  degrade.
- **Agent in the loop.** The alignment or invariant is proposed by an agent
  (or, as a baseline, by a heuristic script); Lean checks it. Record success
  rate, time and tokens, and the pairs where no decomposition was found.

**Acceptance.** At least one pair from the optimiser-output benchmark where
QCEC, PyZX and Feynman all fail within the protocol's limits and a
compositional proof checks — the project's first S. Proof-checking time linear
in circuit size on the aligned pairs. A written account of the pairs where no
alignment or invariant was found, since a systematic failure there would
falsify the hypothesis for that optimiser.

**Delivers.** S. **Harder because** the creative step is not under our
control; whether an agent finds the alignment on real optimiser output is the
most interesting open question in the project.

### Rung 5 — A complete, certified Clifford decision procedure

**Goal.** Decide equivalence of Clifford circuits at hundreds to thousands of
qubits, with a witness on failure, and represent Clifford residuals for Rung 4.

**Work.** Tableau semantics: a Clifford circuit maps to a symplectic matrix over
`𝔽₂` plus a sign vector. The theorem that the tableau determines the unitary up
to phase (Paulis span the matrix algebra, so the commutant is scalar);
completeness (equal tableaux imply `≡ₚ`); a Pauli witness `P` with
`U₁ P U₁† ≠ U₂ P U₂†` on refutation; kernel evaluation in `ZMod 2` packed as
`Nat` bit rows; hooks into QECLean's binary-symplectic layer.

**Acceptance.** GHZ/cat-state ladders and stabilizer-state preparation
circuits for QECLean's codes at `n ≥ 100` verified in seconds; a wrong pair
yields a concrete Pauli; a Rung 4 residual proof uses a Clifford invariant.

**Delivers.** S for Clifford-heavy circuits against non-tableau checkers, and
T. **Harder because** the soundness theorem is real linear algebra over ℚ(ζ₈),
and the procedure has to be fast in the kernel, not merely correct.

### Rung 6 — The classical reversible layer: adders and multi-controlled gates for all `n`

**Goal.** The first parametric templates, and through them S on their
instances.

**Work.** A predicate for circuits of `X`, `CNOT` and Toffoli, with Toffoli a
macro for its 15-gate Clifford+T decomposition verified once at `n = 3` and
lifted by the locality theorem; the theorem that such a circuit permutes basis
states by a Boolean function built compositionally; `≡ᵤ` on classical circuits
reduced to equality of Boolean functions; induction principles for ripple
structures.

**Acceptance.**
`∀ n, cuccaroAdder n ≡ vbeAdder n` (Cuccaro 2004 against Vedral–Barenco–Ekert
1996, up to layout permutation); `∀ n, barencoCnX n ≡ᵃ cnX n` (multi-controlled
`X` via Toffolis with ancilla against its specification, ancilla-aware);
`∀ n, cnotLadder n ≡ᵤ [CX 0 n]`. Fixed-`n` instances run through the benchmark
protocol for the crossover table.

**Delivers.** P, and S at the crossover `n` (probably 32–64, where the T-count
reaches the hundreds). **Harder because** the proofs are inductions with
carry-chain invariants: the first place an agent must do mathematics rather
than evaluation.

### Rung 7 — Agent milestone A: reproduce, then extend

**Goal.** Establish that an agent can drive the library, on both proof shapes.

**Work.** A harness that gives an agent (Claude, Aristotle, or similar) a
statement, the library and the lean-lsp tools, and records outcome, time and
tokens; a held-out set of the existing parametric theorems with proofs
removed; a held-out set of optimiser-output pairs from Rung 4.

**Acceptance.** At least 80 % of the Rung 0–6 parametric theorems re-proved
unaided from statements; at least half of the held-out optimiser pairs proved
compositionally with an agent-found alignment; at least one new parametric
identity found and proved that no human wrote; a written account of every
failure mode observed.

**Delivers.** The evidence for the project's central bet. **Harder because**
success is, for the first time, not under our control.

### Rung 8 — Dyadic rotations and the Fourier layer: QFT and the QFT adder for all `n`

**Goal.** Leave Clifford+T. The QFT needs rotations by `2π/2^k` for `k` up to
`n`, so the coefficient field grows with `n`.

**Work.** Gates `Rz(k) = diag(1, ζ_{2^k})` and their controlled versions;
coefficients either in a tower `ℚ(ζ_{2^m})` or, better, as phase polynomials
with exponents in `ZMod (2^m)`; a certified normaliser for the CNOT + diagonal
fragment, where equivalence is exactly equality of a linear reversible map plus
a phase polynomial, so that fragment gets a *complete* procedure and Rung 4's
latent-algebra mechanism gets its tool; the Fourier lemma that the QFT
diagonalises addition.

**Acceptance.** `∀ n, qft n ≡ᵤ qftSpec n` (recursive circuit against the DFT
matrix); `∀ n, qft n ++ qftInv n ≡ᵤ []`; `∀ n, draperAdder n ≡ cuccaroAdder n`,
a proof that crosses the Fourier and classical layers.

**Delivers.** P, and S on instances. **Harder because** the coefficient ring
is no longer fixed, and the key lemma is a piece of mathematics, not a rewrite.

### Rung 9 — Symbolic parameters: gate-set translations and Trotter steps for all `θ`

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

### Rung 10 — QEC circuits on the code subspace, with QECLean

**Goal.** The project's home turf: encoders, transversal gates and syndrome
extraction as unitary equivalences on a code space.

**Work.** Import stabilizer codes from QECLean; define "implements the logical
gate" and "equivalent modulo the stabilizer group" as circuit-level relations;
apply the classical layer from Rung 6 to CNOT syndrome-extraction schedules;
use QECLean's parametric toric and rotated-surface families for statements in
the lattice size `L`.

**Acceptance.** Every transversal-gate circuit in QECUnitaryCircuits proved as
a logical-gate theorem: Steane `H`, `S`, `CNOT`, and `[[15,1,3]]` transversal
`T` as logical `T`; the Chamberland–Cross flag circuit equivalent on the code
space to its non-fault-tolerant version; `∀ L`, the toric-code
syndrome-extraction schedule maps code states with `|0⟩` ancillas to code
states carrying the syndromes.

**Delivers.** P and T in a domain where no checker has the vocabulary, and S
on the fault-tolerant instances, which are large and Clifford-heavy. **Harder
because** the relations are subspace-relative and the codes are parametric;
Rungs 3, 5 and 6 are all load-bearing.

### Rung 11 — Agent milestone B, and the benchmark

**Goal.** An unaided beyond-SOTA theorem, and an honest public comparison.

**Work.** The agent proves a new Rung 8 or Rung 10 theorem given only the
statement and the library; the benchmark protocol is run in full on both
benchmark families and published with the crossover table; a write-up of the
method.

**Acceptance.** One theorem of type P proved end to end by the agent and
merged; the crossover table shows S on at least one template family and on
the optimiser-output benchmark.

### Rung 12 — Summit: arithmetic for Shor, for all `n`

**Goal.** A theorem whose fixed-`n` instances have thousands of qubits and
millions of gates.

**Work.** Controlled modular multiplication as in Beauregard (QFT-based)
against a Toffoli-based implementation, equivalent for all `n`; components of
windowed arithmetic in the Gidney–Ekerå style. Rungs 6, 8 and 9 combine here.

**Acceptance.** `∀ n, modMulBeauregard n a N ≡ modMulToffoli n a N` on the
relevant subspace, with `a` and `N` symbolic where the mathematics allows.

**Delivers.** P at a scale where S is automatic: no checker can state or
approach it.

## The S-critical path

Rungs 1 → 3 → 4 → 5 are the direct route to the first real-world result, with
the locality theorem as the first concrete deliverable of Rung 4. Rungs 6 and
8 feed templates and the phase-polynomial normaliser back into Rung 4's
mechanisms. Everything else strengthens P or T.

## Benchmark protocol (how S is measured)

Two benchmark families.

- **Template instances.** For each parametric family: fixed-`n` instances at
  `n = 4, 8, 16, 32, 64, 128`. Our result covers all `n` by one proof; report
  the smallest `n` at which each tool fails as the crossover.
- **Optimiser output.** For each origin circuit: the pair (origin, optimised)
  from PyZX `full_reduce` plus extraction, from a T-count optimiser, and from
  Qiskit at optimisation level 3. These are the structurally different,
  T-heavy pairs. This family is the S benchmark proper.

Tools: QCEC (`mqt.qcec`), PyZX (`full_reduce` on `U†V`, and `compare_tensors`
where feasible), Feynman (`feynver`), and any newer checker such as the one
QECUnitaryCircuits targets. One-hour timeout, 16 GB. Record pass, fail or
timeout, and time. Report honestly that on compilation-flow pairs, where the
two circuits are structurally close, decision-diagram tools will beat kernel
checking at every `n`; the advantage there is T, not S.

## Cross-cutting tracks

- **Performance.** Reflection, packed `Nat`, no `Finset.sum` in anything the
  kernel evaluates; measured on every rung.
- **Trust, proportionate.** Semantics reviewed by hand and pinned by identity
  lemmas; the evaluator proved, not tested; the generator conformance-checked
  against Qiskit in CI; the axiom policy in CI. Nothing uses `native_decide`.
- **Flywheel.** Every proved equivalence is a lemma. Keep `Structural.lean`
  curated, grow a `simp` set, and record which lemmas agents actually reach for
  and which alignments they find.
- **Documentation.** Each rung lands with a short design note.

## Dependencies

Rung 1 before 4 and 5. Rung 2 alongside 1. Rung 3 before 4, 6 and 10. Rung 4
before 7. Rung 5 before 10, and it strengthens 4. Rung 6 before 8, and 8
before 12. Rung 9 before 12. Rung 8 strengthens 4. Rung 11 after 8 or 10.

## Risks and fallbacks

- **No alignment or invariant found on some optimiser's output.** Fall back
  to brute force at Rung 1 sizes or to replaying the certificate the external
  tool produced. A systematic failure is a finding about that optimiser, and
  narrows the hypothesis rather than the project.
- **Kernel performance wall.** Fallback: a clearly labelled second trust tier
  using `native_decide` for concrete checks only, never for library lemmas.
- **A parametric target needs new mathematics.** That is the point; scope the
  acceptance test to what is provable and record the rest as conjectures.
- **Coefficient-field growth in Rung 8.** Prefer phase polynomials to a tower
  of fields.
- **Agent reliability.** The library and decision procedures have standalone
  value; the agent rungs are evidence, not prerequisites.
- **Generator convention drift.** The Rung 2 conformance check is cheap; keep
  it in CI.

## Suggested order for the next quarter

Rung 1, then 2, then 3, then 4 starting with the locality theorem, then 6 and
7. Take Rung 5 as soon as a Rung 4 residual proof needs a Clifford invariant.
The first S result from Rung 4 is the first thing worth writing up.
