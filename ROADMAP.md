# Roadmap — a ladder from toy identities to circuits no checker can reach

The target is proving equivalence of *useful, real-world* quantum circuits
that current automated equivalence checkers cannot handle, first as an
AI + Lean equivalence checker and, in the longer run, as an AI + Lean
optimiser that finds an optimisation and proves it (see "Two products, one
architecture"). This document breaks that into rungs of increasing
difficulty. Each rung has a concrete acceptance test, so progress is
measurable, and each leaves reusable library behind, so the rungs above it
get cheaper. They are ordered by difficulty and dependency; they need not be
finished strictly in sequence.

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

### Which equivalence relation

Basic equivalence carries most of the project. `≡ᵤ` (equal unitaries) and
`≡ₚ` (equal up to a global phase) already exist and are decidable, and they
are all the S-critical path needs:

- optimisers preserve the whole unitary up to a global phase, so
  optimiser-output pairs are `≡ₚ` statements;
- routing appends a permutation of the qubits, and a permutation is a SWAP
  network, which is a circuit: a routed circuit is verified as
  `compiled ≡ₚ source ++ swapNetwork π` with `π` read from the transpiler's
  metadata. No new relation is needed.

Refined relations — equivalence on the subspace where ancilla qubits are `|0⟩`,
equivalence up to a relative phase on a subspace, equivalence modulo a
stabilizer group — are needed only to compare *different constructions* that
use ancillas (two multi-controlled-`X` decompositions, two adders with
different ancilla counts, a relative-phase Toffoli inside a gadget) and for
statements on a code subspace. The decidable part of each is easy: the same
basis check over fewer basis vectors. The algebra is where care is needed,
because equivalence on a subspace is a congruence for sequencing only when the
surrounding circuit preserves that subspace, so every congruence lemma carries
a side condition. They are therefore introduced at Rung 5, immediately before
the constructions that need them, and only in the form those constructions
need.

### What "structure" means for compiled circuits

This is the project's working hypothesis. Rung 3 is its test.

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
  independent of `n`, given the locality theorem of Rung 3. Finding the
  alignment is the creative step; QCEC's alternating scheme does it by a fixed
  heuristic, and that is exactly the freedom an agent adds.
- **Residual invariants.** At agent-chosen cut points, assert that one
  circuit's prefix times the inverse of the other's is something compact — a
  Clifford, a diagonal — and prove each step preserves it. This is a loop
  invariant; tools cannot invent them, agents and humans do routinely. The
  tableau layer of Rung 4 is what represents a Clifford residual compactly.
- **Latent algebra.** Between Hadamard layers every Clifford+T circuit is a
  CNOT-plus-diagonal fragment with a canonical phase-polynomial form. An agent
  can reason in that form across the Hadamard boundaries, case by case, where
  a fixed reduction system stalls. The normaliser of Rung 8 is the tool.

## Two products, one architecture

The project has two goals, and it pays to keep them distinct because the
agent searches for different things in each.

- **The equivalence checker.** Input: two circuits. Output: a kernel-checked
  proof of `≡ᵤ` or `≡ₚ`, a kernel-checked refutation, or "no certificate
  found", recorded. The agent's search is for a *derivation between two
  fixed endpoints* that nobody handed it: an optimiser produced the second
  circuit and discarded the path. This is the S benchmark of the ladder.
- **The optimiser.** Input: one circuit. Output: a cheaper circuit and a
  kernel-checked proof that it is equivalent. The agent's search is for a
  *cheaper endpoint*, and since it chooses every step, the derivation is
  known and the proof is free. Correctness is guaranteed by construction
  whatever strategy chose the steps, so the strategy can be anything: model
  judgment, heuristics, search. Only quality is at stake, never soundness.

The checker is a subroutine of the optimiser, and every optimiser step is a
checker move: a derivation from `c₁` to `c₂` by certified steps is a proof
of their equivalence, and the checker's hard case is exactly reconstructing
a derivation an external tool discarded. The optimiser avoids that case by
construction, which makes it the more tractable product in the long run. The
checker is built first because it is what lets the optimiser absorb external
tools' results instead of competing with them.

What the optimiser certifies is `c ≡ᵤ c'` (or `≡ₚ`) together with a cost
computed in Lean, `tCount c' = k` (`QUEUE.md`, item 2). It does not certify
optimality: nothing proves that no cheaper circuit exists. Quality is
reported by comparison, the certified T-count against the uncertified
T-count of TZAP and PyZX on the same input. The agent may call those tools,
but it must certify whatever it ships.

### What is strictly needed, and what the library adds

Stated minimally, the checker's problem is: given Clifford+T circuits `c₁`
and `c₂`, produce a Lean proof of `c₁ ≡ᵤ c₂` or `c₁ ≡ₚ c₂`, or of the
negation. Three things are strictly needed for that, and they are the
trusted part.

- A semantics for the gate set: `Gate1.mat`, `applyOne`, `applyCNOT`,
  `denote`.
- The definition of the relation: `≡ᵤ`, `≡ₚ`.
- A rule for what counts as a proof: the statement as given, checked by the
  kernel, on `[propext, Classical.choice, Quot.sound]`, with no
  `native_decide` and no `sorry`. The agent harness enforces this
  mechanically (`QUEUE.md`, item 1), because an agent under a time limit
  reaches for exactly those shortcuts.

Everything else in the library is optional in principle. An agent is free
to prove the statement however it likes, new lemmas and new checkers
included, and anything the kernel accepts counts. The library exists for
two independent reasons.

- **Finding proofs.** Today's agents do not develop a tableau or a
  phase-polynomial normal form inside one proof attempt. Lemmas that split
  and recombine circuits (`Equivalent.append`, `Equivalent.in_context`,
  `rename_equivalent_iff`), checked rewrites (`Instr.CanCommute`,
  `Instr.CanCancel`, fusion) and certified fragment checkers are the
  vocabulary that makes the search tractable. That this vocabulary lets
  agents prove larger and deeper pairs is a hypothesis, and it is measured
  rather than assumed: the harness runs one prompt under one set of limits
  against the library as it grows, and against the trusted modules alone.
- **Checking proofs.** This reason does not go away with a better agent. The
  kernel cannot finish a seven-qubit basis check as one declaration (chunked it
  can, but the cost grows as `gates · 4^n`; `benchmarks/scale/README.md`), and a
  proof term assembled gate by gate is quadratic, so any agent, however capable,
  has to route a large concrete proof through reflection: a computable
  structure, a soundness theorem, one kernel evaluation. The library amortises
  what every agent would otherwise rebuild. This is why, for concrete circuits,
  the supported path is a certificate, data replayed by `replay_sound`, and the
  agent's freedom is spent on finding the structure (the alignment, the cut
  points, the template instance). Free-form Lean is for parametric theorems and
  for the `calc` that composes around a certificate.

Where the infrastructure stands against that problem statement
(18 September 2026, updated 22 September), so that nobody over-reads it:

- **Three relations exist, not two.** The tableau certifies `≡ₛ`, equality
  up to a unit of `Zeta8`. `Zeta8` is a field, so that is any nonzero
  scalar, and it is weaker than `≡ₚ` until the scalar of a Clifford pair is
  proved to be a power of `ω` (open, Rung 4). Certificates and
  `circuit_windows` state `≡ᵤ`, `≡ₚ` and `≡ₚ[k]` (since `83cc1d7`),
  so a pair equal only up to a global phase is proved window by window; the
  tableau cannot justify such a window until the `≡ₛ` half of the scalar
  replay (`QUEUE.md`, item 13) and `≡ₛ → ≡ₚ` for Clifford circuits land.
- **The fragments are narrower than their names.** The phase-polynomial
  checker covers `CX` with `Z, S, S†, T, T†`: `H` ends the fragment, and
  for now so do `X` and `Y` (`QUEUE.md`, item 8). On that fragment it is
  sound and complete, so it also refutes. The tableau covers `CX` with the
  single-qubit Cliffords and is sound; its completeness is open, so a
  differing tableau is a witness and not yet a kernel-checked refutation.
- **The target is optimiser output, not arbitrary pairs**, for the reasons
  under "What 'structure' means for compiled circuits", and the measure is
  S against QCEC, PyZX and Feynman, with gate-deleted mutants refuted
  alongside. A benchmark "of increasing complexity" therefore means
  optimiser pairs of increasing size and structural distance (reordering,
  then phase teleportation and TZAP, then `full_reduce` and Qiskit at
  level 3), not random pairs.

### The architecture both share

1. **A trusted core.** `denote` over state vectors and the definition of
   `≡ᵤ`, reviewed by hand, pinned by identity lemmas, never evaluated at
   scale, never redefined.
2. **A certificate language.** A Lean data type of rewrite steps: swap two
   adjacent commuting gates; cancel a pair; replace a window by an
   equivalent window on `k` wires; normalise a Clifford or CNOT-plus-diagonal
   block; substitute a template instance by an equivalent one proved for all
   `n`. Every new proof technique lands as a step kind.
3. **A replay interpreter with a soundness theorem.** `replay steps c` is a
   circuit and `c ≡ᵤ replay steps c` for every well-formed trace. The kernel
   runs the interpreter; the proof term is one application of the theorem;
   cost is linear in the trace. The agent emits *data*, never proof terms,
   so the same steps can run fast outside Lean during search, with Lean as
   the judge.
4. **Certified checkers behind the steps.** Tableaux for Clifford blocks,
   phase polynomials for CNOT-plus-diagonal blocks, Boolean functions for
   classical reversible blocks, the small-window evaluator on at most a
   dozen qubits. Each verifies a tool's *answer*, never its algorithm, so a
   new optimiser costs nothing to support and nobody reads its source. ZX
   rewriting itself resists this, since a ZX derivation lives on diagrams;
   its output is caught by the fragment checkers and residuals instead.
5. **Representations built for the checkers.** Gates and blocks carry their
   wire sets as `Nat` bitmasks, so a commutation test is one `land`.
   Circuits are hierarchical, named blocks and templates parametric in `n`
   with congruence lemmas, and the flat list exists only for `denote`.
   Large concrete circuits enter as compact data the kernel decodes. Routing
   is a wire relabelling; ancilla subspaces are a side condition on
   congruence. Cost functions (T-count, depth, gate count) are computed in
   Lean, so "this circuit has T-count 19" is a checked claim (none exists
   yet: `QUEUE.md`, item 2).
6. **The agent.** External tools (TZAP, PyZX, Feynman, quizx, Qiskit) are
   untrusted oracles it uses to see where the structure is. It never sees a
   million gates; it works at the level of blocks and delegates below that
   to checkers. Its output is a certificate; Lean's error messages are its
   feedback.

The optimiser runs in two modes. *Constructive*: apply certified steps and
ship the trace. *Oracle-guided*: run an external optimiser, take its output
as the target, certify it with the checker, and fall back to constructive
mode steered by the target if certification fails. The hybrid is the aim:
external optimisations verified when possible, the agent's own otherwise.

**TZAP is the model oracle.** TZAP (Albarghouthi, arXiv 2605.13929) does
phase folding in linear time by replacing the exact parity analysis of
Feynman and VOQC with random 128-bit fingerprints per wire: CNOT XORs
them, `H` draws a fresh one, and rotations whose wires carry equal
fingerprints merge. It matches the T-count of PyZX, VOQC, QuiZX and
Feynman within a few percent, runs orders of magnitude faster (148 million
gates in under a minute), is sound only with probability `1 − m²·2⁻¹²⁸`,
and validates its output by matrix comparison up to six qubits and by
Feynman's path-sum verifier on some larger circuits: no certificate. Its
symbolic variant is exactly the analysis `CircuitEq/PhasePoly.lean`
certifies, and its output keeps the CX/H/X skeleton (it only deletes
rotations, edits angles and cancels `XX`/`HH` pairs), so a TZAP pair is
alignable by construction. The optimiser's oracle-guided mode is therefore
concrete: run TZAP in milliseconds, certify in the kernel with the
phase-polynomial checker extended by Hadamard variables (`QUEUE.md`,
item 4), and never rely on the `2⁻¹²⁸`. The Feynman and Cobble suites it
is evaluated on are the T-heavy benchmark family Rung 3 asks for.

**Parametric proofs are not displaced.** A theorem for all `n` is an
ordinary Lean statement about a circuit family, proved by induction with
the structural toolkit, and it meets certificates in two ways: around one,
as in the Steane proof, where a `calc` applies the parametric block theorem
and a certificate closes the concrete remainder; and inside one, as the
template step, which applies a registered theorem proved for all `n` at a
concrete `n` with no evaluation at all. The one constraint is that a
certificate step can only name a *registered* lemma, because `replay` is
fixed code driven by data, so a new parametric identity is used by
registering it or by composing around the certificate. The P method stays
the way to reach large `n`; certificates are how its instances and the
concrete leftovers get checked.

Where this stands (22 September 2026): the certificate language exists
(`CircuitEq/Certificate.lean`: `Step`, `replay`, `replay_sound`, a checker
table, and `replayPhase` / `replayPhase_sound`, which read the same steps up
to a global phase and name it), and `circuit_windows` and `circuit_simp` emit
its traces and close `≡ᵤ`, `≡ₚ` and `≡ₚ[k]` goals with one replay. Two
fragment checkers are behind it, the phase polynomial (`PhasePoly.lean`,
`≡ᵤ`) and the Clifford tableau (`Tableau.lean`, `≡ₛ`), the basis evaluator
runs on the gcd-free ring (`Dyadic.lean`), and a Python mirror of the
language exists. The agent harnesses exist as drafts with one proved run
(`benchmarks/harness/`). What is missing is in `QUEUE.md`: repeated
harness runs, cost functions in Lean, the `≡ₛ` half of the scalar replay so
tableau windows and residuals compose, Hadamard variables in the phase
polynomial, and the template step for registered parametric lemmas.

## The ladder

### Rung 0 — Prototype ✅ (September 2026)

Computable ℚ(ζ₈); sparse state-vector semantics; `≡ᵤ` and `≡ₚ` decidable for
concrete circuits; a structural toolkit; twenty identities, several parametric
in `n` (`hLayer_hLayer`, `T_cnot_comm`, `H_T_H_eq_T`).

Limits: the gate alphabet is single-qubit Clifford+T plus CNOT; concrete
checks cost `2^depth`; there is no link to ℂ; no locality theorem, so every
`decide` pays for all `n` qubits.

### Rung 1 — Concrete circuits at benchmark scale

**Status (16 September 2026).** The evaluator and the compact coefficient
ring are both in: the `Decidable` instances run a closure evaluator over
`Dyadic8` (`CircuitEq/Dyadic.lean`, the ring `ℤ[ω, 1/√2]`, no gcd), proved
equal to `denote`, with the list evaluator `evalList` kept as the reference
form. A three-qubit six-gate window went from 3 s to 0.09 s and depth is
linear. The seven-qubit `SteanePlus` basis decide is memory-bound: on an
idle 16 GB machine a 6 GB watchdog killed it after 20 s at 6.9 GB resident
and still growing (the kernel's `whnf` cache retains everything evaluated
in one declaration). Chunked evaluation (`CircuitEq/Chunk.lean`, one basis
vector per declaration) now decides it in 78 s at 1.98 GB; the cost grows
as `gates · 4^n`, so the 10–12-qubit acceptance below is still hours by
evaluation, and for the Clifford benchmark family the route is the tableau
of Rung 4 instead. `swapNetwork`, mutants and the
Qiskit-routed pairs have not been attempted.

**Goal.** Decide `≡ᵤ` and `≡ₚ` for concrete Clifford+T circuits of the size
real benchmarks have: 10–12 qubits, depth in the hundreds to low thousands.

**Work.** A materialised evaluator over `List`/`Array`, gate by gate, so cost
is `O(depth · 2^n)` instead of `O(2^depth)`; a *proof* that it agrees with
`denote` (its correctness is a theorem, not a test); a `Decidable` instance
routed through it. If ℚ's gcd normalisation dominates, re-represent `Zeta8` as
ℤ numerators over a shared power of √2 (the exact-synthesis ring `D[ω]`).
Packed `Nat` bit-vectors where lists are too slow for the kernel — the
technique that de-nativised QECLean's gross-code proof. A `swapNetwork π`
circuit and the derived statement for routed circuits.

**Acceptance.** Verify all 19 origin circuits of QECUnitaryCircuits against
their PyZX-optimised twins, and refute their gate-deleted mutants, each in
under one minute of kernel time. Verify Qiskit-transpiled versions of the same
circuits, with routing SWAPs and layout changes, against their sources via
`≡ₚ … ++ swapNetwork π`, at the sizes the evaluator reaches. Publish the
scaling table (n, depth, seconds).

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

### Rung 3 — Compositional proofs of fixed-size pairs

**Status (16 September 2026).** The hypothesis has its first test,
`benchmarks/survey/`: eleven T-heavy circuits against PyZX phase
teleportation and `full_reduce`, aligned by a diff-based script and checked
by `circuit_windows`. Teleportation output aligns by windows on the
structured circuits: `tof_3`, `tof_4`, `barenco_tof_3`, `cuccaro_2` and
`cuccaro_3` are kernel-checked in 2 to 10 s each on the dyadic evaluator
(`barenco_tof_3` is promoted as a benchmark, six one-wire windows the
script found unaided), `cuccaro_4` is memory-bound in the replay of a
155-gate certificate, and `tof_5` finds no alignment within eight wires
because a `CZ` commuted through control-only blocks is not a gate-by-gate
move. Re-synthesised output never aligns except as a whole-register decide
(`mod5_4`, `random_4q`, `cuccaro_2`), which proves the pair but says
nothing about locality. Three random pairs are equal only up to a global
phase, which `circuit_windows` could not state at the time; it now accepts
`≡ₚ` and `≡ₚ[k]` goals, with windows that hold up to a phase of their own,
though those three pairs have no alignment either way. The decisive observation
for what comes next: every wide window of the structured pairs is one or two
CNOT-plus-diagonal segments around a single interior Hadamard, each an
equivalence on its own, so with the phase-polynomial checker as the leaf and
windows cut at common Hadamard layers, the structured teleportation pairs
become proofs with no basis decide wider than one wire (`QUEUE.md`,
item 7). The residual pattern is still what `full_reduce` output needs.

**Goal.** The direct route to S on real compiled circuits, and the empirical
test of the working hypothesis above. Everything here is stated with `≡ᵤ` and
`≡ₚ`.

**Work.**

- **The locality theorem.** ✅ (September 2026, `CircuitEq/Embedding.lean`:
  `rename_equivalent_iff`.) If two sub-circuits touch only a set of `k`
  qubits, their equivalence on `n` qubits is equivalent to the equivalence of
  their restrictions on `k` qubits. Gate placement is `rename f` for an
  embedding `f : Fin k ↪ Fin n`; this is what makes a window cost `2^k`
  instead of `2^n`.
- **The window pattern.** Given an alignment — a matching of windows between
  the two circuits, plus the commutations needed to make them adjacent — a
  tactic or macro discharges the whole equivalence by congruence, moving
  lemmas, and one small `decide` per window. The alignment is *input*; the
  tactic only checks it. ✅ (September 2026.) `circuit_windows` in
  `CircuitEq/Tactic.lean` takes the alignment as a list of windows, decides
  each on its own wires (`Equivalent.of_rename`, cost `2^k`), and checks
  every move (`pull_cons`); `circuit_simp` is the same engine without
  windows. The block theorems of `CircuitEq/Layers.lean` closed the first
  two QECUnitaryCircuits-versus-PyZX pairs, and `circuit_windows` closed
  `tof_3` against PyZX phase teleportation (T-count 21 → 19) with four
  windows on at most three wires (`CircuitEq/Benchmarks/`). Re-synthesised
  output (`full_reduce`, T-count 15 on the same input) has no alignment;
  that is the residual pattern's job.
- **The certificate language and replay interpreter.** ✅ (16 September
  2026, `CircuitEq/Certificate.lean`.) `Step` (`swap`, `moveLeft`,
  `moveRight` across a block with disjoint bitmask support, `cancel`,
  `insert`, `window` on named wires justified by a checker from a table),
  `replay`, `replay_sound` for every table; the tactics emit traces and
  close with one `replay_sound`; `scripts/certificate.py` mirrors it.
  Missing: cursor-based traces (replay still walks to each position), the
  template step, and the `≡ₛ` variant that lets tableau windows compose.
- **The residual pattern.** Cut points with a compact residual (diagonal
  first; Clifford once Rung 4 lands), proved preserved step by step.
- **The optimiser-output benchmark.** For each of the 19 QECUnitaryCircuits
  origins, and for adders and QFTs at `n = 8` to `64`: the output of PyZX
  `full_reduce` plus extraction, of a T-count optimiser (TZAP first, whose
  phase-folding output keeps the gate skeleton and is alignable by
  construction, then quizx or Feynman), and of Qiskit at optimisation
  level 3. These pairs are structurally different and T-heavy, which is
  where decision-diagram tools degrade. TZAP's own benchmark inputs, the
  Feynman suite (`gf2^k_mult`, `mod_adder`, `barenco_tof`, `hwb`, …) and
  the Cobble suite, are the natural T-heavy sources at the sizes the kernel
  reaches.
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

### Rung 4 — A complete, certified Clifford decision procedure

**Status (16 September 2026).** The tableau is in: `CircuitEq/Tableau.lean`
conjugates the `2n` Pauli generators (x-mask, z-mask, phase in `Fin 4`)
through `H, X, Y, Z, S, S†, CX` with `O(n)` bit operations per gate, and
`tableau_sound` proves equal tableaux give `≡ₛ` by the commutant argument
on state vectors, with a `witness` function naming the first disagreeing
generator. The 15-qubit Reed–Muller encoder against its PyZX
re-synthesis decides in about 0.3 s of kernel time
(`CircuitEq/Benchmarks/RM15Zero.lean`). Open: completeness, the `≡ₚ`
strengthening (the scalar is a power of `ω`; number theory in `ℤ[ω]`), the
19-origin run, and the residual use in Rung 3 (`QUEUE.md`).

**Goal.** Decide equivalence of Clifford circuits at hundreds to thousands of
qubits, with a witness on failure, and represent Clifford residuals for Rung 3.

**Work.** Tableau semantics: a Clifford circuit maps to a symplectic matrix over
`𝔽₂` plus a sign vector. The theorem that the tableau determines the unitary up
to phase (Paulis span the matrix algebra, so the commutant is scalar);
completeness (equal tableaux imply `≡ₚ`); a Pauli witness `P` with
`U₁ P U₁† ≠ U₂ P U₂†` on refutation; kernel evaluation in `ZMod 2` packed as
`Nat` bit rows; hooks into QECLean's binary-symplectic layer.

**Acceptance.** GHZ/cat-state ladders and stabilizer-state preparation
circuits for QECLean's codes at `n ≥ 100` verified in seconds; a wrong pair
yields a concrete Pauli; a Rung 3 residual proof uses a Clifford invariant.

**Delivers.** S for Clifford-heavy circuits against non-tableau checkers, and
T. **Harder because** the soundness theorem is real linear algebra over ℚ(ζ₈),
and the procedure has to be fast in the kernel, not merely correct.

### Rung 5 — Refined equivalence, only as constructions need it

**Goal.** The relations required to compare different ancilla-using
constructions, introduced in the minimal form the next rungs need.

**Work.** Equivalence on the ancilla subspace (the last `a` qubits enter in
`|0⟩`; a variant also requires them to leave in `|0⟩`); equivalence up to a
relative phase on a subspace, for Margolus-style relative-phase Toffolis. For
each: the decidable basis-check form, and congruence lemmas *with their side
conditions* (the surrounding circuit must preserve the subspace). Nothing is
defined until a Rung 6 or Rung 10 statement needs it, and permutation stays a
derived notion via `swapNetwork`.

**Acceptance.** A Toffoli-with-ancilla decomposition verified against its
specification on the `|0⟩`-ancilla subspace; the 4-T relative-phase Toffoli
verified against Toffoli under the relative-phase relation; the congruence
lemmas proved with explicit side conditions.

**Delivers.** The prerequisites for Rungs 6 and 10; nothing on the S-critical
path depends on it. **Harder because** the definitions are subtle — what
"restored ancilla" means on superposed inputs, when sequencing is a congruence
— and a wrong one silently weakens everything built on it.

### Rung 6 — The classical reversible layer: adders and multi-controlled gates for all `n`

**Goal.** The first parametric templates, and through them S on their
instances.

**Work.** A predicate for circuits of `X`, `CNOT` and Toffoli, with Toffoli a
macro for its 15-gate Clifford+T decomposition verified once at `n = 3` and
lifted by the locality theorem; the theorem that such a circuit permutes basis
states by a Boolean function built compositionally; `≡ᵤ` on classical circuits
reduced to equality of Boolean functions; induction principles for ripple
structures. Layout differences are handled by `swapNetwork`; ancilla-count
differences by the Rung 5 subspace relation.

**Acceptance.**
`∀ n, cuccaroAdder n ≡ vbeAdder n` (Cuccaro 2004 against Vedral–Barenco–Ekert
1996, on the ancilla subspace after layout alignment);
`∀ n, barencoCnX n ≡ᵃ cnX n` (multi-controlled `X` via Toffolis with ancilla
against its specification); `∀ n, cnotLadder n ≡ᵤ [CX 0 n]`. Fixed-`n`
instances run through the benchmark protocol for the crossover table.

**Delivers.** P, and S at the crossover `n` (probably 32–64, where the T-count
reaches the hundreds). **Harder because** the proofs are inductions with
carry-chain invariants: the first place an agent must do mathematics rather
than evaluation.

### Rung 7 — Agent milestone A: reproduce, then extend

**Status (21 September 2026).** A draft harness exists (`benchmarks/harness/`,
`QUEUE.md` item 1, pulled forward so that the agent is measured while the
library grows rather than after Rung 6): three runs on one held-out
1000-gate pair on 19 September, the third proved; an optimiser harness built
on the same pieces, not yet run; and a catalogue of 147 real circuits with
390 measured pairs as the held-out ladder (`benchmarks/circuits/`). Before
those runs every alignment was found by a person or by the survey's diff
script. The acceptance below is unchanged; the early runs are the baseline
it is read against.

**Goal.** Establish that an agent can drive the library, on both proof shapes.

**Work.** A harness that gives an agent (Claude, Aristotle, or similar) a
statement, the library and the lean-lsp tools, and records outcome, time and
tokens; a held-out set of the existing parametric theorems with proofs
removed; a held-out set of optimiser-output pairs from Rung 3.

**Acceptance.** At least 80 % of the Rung 0–6 parametric theorems re-proved
unaided from statements; at least half of the held-out optimiser pairs proved
compositionally with an agent-found alignment; at least one new parametric
identity found and proved that no human wrote; a written account of every
failure mode observed. And the optimiser's first outing: a held-out set of
circuits optimised in constructive mode by certified steps, reporting the
certified T-count against PyZX's uncertified T-count on the same inputs.

**Delivers.** The evidence for the project's central bet. **Harder because**
success is, for the first time, not under our control.

### Rung 8 — Dyadic rotations and the Fourier layer: QFT and the QFT adder for all `n`

**Goal.** Leave Clifford+T. The QFT needs rotations by `2π/2^k` for `k` up to
`n`, so the coefficient field grows with `n`.

**Work.** Gates `Rz(k) = diag(1, ζ_{2^k})` and their controlled versions;
coefficients either in a tower `ℚ(ζ_{2^m})` or, better, as phase polynomials
with exponents in `ZMod (2^m)`; a certified normaliser for the CNOT + diagonal
fragment, where equivalence is exactly equality of a linear reversible map plus
a phase polynomial, so that fragment gets a *complete* procedure and Rung 3's
latent-algebra mechanism gets its tool; the Fourier lemma that the QFT
diagonalises addition. The `Fin 8` version of the normaliser exists for the
Hadamard-free fragment (`CircuitEq/PhasePoly.lean`, September 2026); the
Hadamard-variable (path-sum) extension and the `ZMod (2 ^ m)` phases are
queued.

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
gate" and "equivalent modulo the stabilizer group" as circuit-level relations,
the one place a relation beyond Rung 5's is needed; apply the classical layer
from Rung 6 to CNOT syndrome-extraction schedules; use QECLean's parametric
toric and rotated-surface families for statements in the lattice size `L`.

**Acceptance.** Every transversal-gate circuit in QECUnitaryCircuits proved as
a logical-gate theorem: Steane `H`, `S`, `CNOT`, and `[[15,1,3]]` transversal
`T` as logical `T`; the Chamberland–Cross flag circuit equivalent on the code
space to its non-fault-tolerant version; `∀ L`, the toric-code
syndrome-extraction schedule maps code states with `|0⟩` ancillas to code
states carrying the syndromes.

**Delivers.** P and T in a domain where no checker has the vocabulary, and S
on the fault-tolerant instances, which are large and Clifford-heavy. **Harder
because** the relations are subspace-relative and the codes are parametric;
Rungs 4, 5 and 6 are all load-bearing.

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

Rungs 1 → 3 → 4, entirely in `≡ᵤ` and `≡ₚ`, with the locality theorem as the
first concrete deliverable of Rung 3. Rungs 6 and 8 feed templates and the
phase-polynomial normaliser back into Rung 3's mechanisms. Rung 5, the refined
relations, is deliberately off this path. Everything else strengthens P or T.

## Benchmark protocol (how S is measured)

Two benchmark families.

- **Template instances.** For each parametric family: fixed-`n` instances at
  `n = 4, 8, 16, 32, 64, 128`. Our result covers all `n` by one proof; report
  the smallest `n` at which each tool fails as the crossover.
- **Optimiser output.** For each origin circuit: the pair (origin, optimised)
  from PyZX `full_reduce` plus extraction, from a T-count optimiser (TZAP,
  then quizx or Feynman), and from Qiskit at optimisation level 3. These
  are the structurally different, T-heavy pairs. This family is the S
  benchmark proper.

Tools: QCEC (`mqt.qcec`), PyZX (`full_reduce` on `U†V`, and `compare_tensors`
where feasible), Feynman (`feynver`), and any newer checker such as the one
QECUnitaryCircuits targets. One-hour timeout, 16 GB. Record pass, fail or
timeout, and time. Report honestly that on compilation-flow pairs, where the
two circuits are structurally close, decision-diagram tools will beat kernel
checking at every `n`; the advantage there is T, not S.

## Cross-cutting tracks

- **Performance.** Reflection, packed `Nat`, no `Finset.sum` in anything the
  kernel evaluates; measured on every rung.
- **Certificates.** Every proof technique lands as a step kind in the
  certificate language with a checker behind it, plus a Python mirror of the
  step so search can run outside Lean. The tactics of `CircuitEq/Tactic.lean`
  already search in meta code and emit certificate traces.
- **Trust, proportionate.** Semantics reviewed by hand and pinned by identity
  lemmas; the evaluator proved, not tested; the generator conformance-checked
  against Qiskit in CI; the axiom policy in CI, and with it the kernel replay
  of the built `.olean` files (`leanchecker`), since an axiom check cannot see
  a declaration that skipped the kernel. Nothing uses `native_decide` or a
  `debug.*` option.
- **Flywheel.** Every proved equivalence is a lemma. Keep `Structural.lean`
  curated, grow a `simp` set, and record which lemmas agents actually reach for
  and which alignments they find.
- **Documentation.** Each rung lands with a short design note.

## Dependencies

Rung 1 before 3 and 4. Rung 2 alongside 1. Rung 3 before 7. Rung 4 before 10,
and it strengthens 3. Rung 5 before 6 and 10. Rung 6 before 8, and 8 before
12. Rung 9 before 12. Rung 8 strengthens 3. Rung 11 after 8 or 10.

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

The concrete, current version of this list is `QUEUE.md`.

The certificate language and replay interpreter with bitmask supports
(Rung 3), since they replace the quadratic tactic and every later technique
is a step kind in them; the gcd-free coefficient ring (Rung 1), which speeds
up every leaf; then the Rung 3 benchmark run over the 19 origins with a
diff-based alignment script as the baseline, recording the pairs with no
alignment, with Rung 2's conformance check riding along because the
translation script is now where a convention error would live. Take Rung 4
as soon as a residual proof needs a Clifford invariant. Then Rung 6,
defining only the parts of Rung 5 that the adders and multi-controlled gates
actually need, then Rung 7 in both checker and optimiser modes. The first S
result from Rung 3 is the first thing worth writing up.
