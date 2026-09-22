# CLAUDE.md — agent orientation

CircuitEq is a Lean 4 / mathlib library for stating and proving unitary
equivalence of Clifford+T quantum circuits. Read `README.md` first for the
pitch and the design; this file is the working conventions. Build with
`lake build`. The next pieces of work, in priority order with context and
acceptance tests, are in `QUEUE.md`; take the top unblocked item and move
it to "Done" when it lands.

## What we are optimising for

Two products, one architecture (`ROADMAP.md`, "Two products, one
architecture"):

1. **An AI + Lean equivalence checker.** Given two circuits, an agent finds
   the structure (an alignment of windows, cut points with residuals, a
   template instance) and Lean checks it. The agent searches for a
   derivation between fixed endpoints that an optimiser discarded.
2. **An AI + Lean optimiser**, longer term. Given one circuit, the agent
   finds a cheaper one by certified rewrite steps and the proof is the
   trace. Soundness is by construction; only quality depends on the agent.

Rules that follow, for anyone adding to the library:

- `denote` and `≡ᵤ` are the trusted core. Never redefine them. Every
  scalable representation is a separate computable structure with a proven
  correspondence, used by reflection: the dyadic evaluator, `rename`,
  `PhasePoly.nf`, `tableau` and `replay` are the pattern.
- Verify answers, not algorithms. A new optimiser is supported by a
  certified normal form or checker for the fragment it works in, never by
  formalising its source. External tools are untrusted oracles: TZAP
  (linear-time phase folding, probabilistically sound, no certificate; its
  output keeps the gate skeleton, so its pairs align by construction),
  PyZX, Feynman, Qiskit.
- New proof techniques land as *step kinds in a certificate language* with
  a certified replay interpreter behind them, so the agent emits data and
  the kernel's cost is linear in the trace. `CircuitEq/Certificate.lean` is
  that language; the tactics in `CircuitEq/Tactic.lean` emit its steps. Do
  not add tactics that assemble proof terms gate by gate.
- Representations are chosen for the checkers: `Nat` bitmasks for wire
  supports, hierarchical circuits with congruence for blocks, templates
  parametric in `n`, cost functions computed in Lean. Nothing of size
  `2 ^ n` is ever built for `n` beyond a window.
- Prefer a lemma stated on `≡ᵤ` for arbitrary `n` over a bigger `decide`.
  `decide +kernel` is the leaf oracle for windows of a few qubits, never
  the plan for large circuits.

## Layout

- `CircuitEq.lean` — umbrella of the library; every library module must be
  imported here or it is never built, never linted, and its errors are
  invisible. `CircuitEqTest.lean` is the same for the second `lean_lib`,
  the examples and the tests: it imports `CircuitEq.Examples` and
  `CircuitEqTest/*.lean`. Both are default targets, so `lake build`, the
  axiom check and the kernel replay cover both; nothing in `CircuitEq`
  imports them.
- `CircuitEq/Zeta8.lean` — `Quantum.Zeta8`, computable ℚ(ζ₈). Constants
  `ω`, `I`, `sqrt2`, `invSqrt2`; identities by `decide +kernel`. Exponents
  of `ω` live in `Fin 8`: `ω_pow_mod`, `ω_pow_val_add` (`ω ^ ↑(j + k) =
  ω ^ ↑j * ω ^ ↑k`) and `ω_pow_val_neg_mul` are what makes global phases
  compose.
- `CircuitEq/Bits.lean` — `bit`, `flipBit` on `Fin (2 ^ n)`; the four lemmas
  `bit_flipBit_self`, `bit_flipBit_of_ne`, `flipBit_flipBit_self`,
  `flipBit_comm` are what every commutation proof rewrites with.
- `CircuitEq/Gates.lean` — `Gate1`, `Gate1.mat : Matrix Bool Bool Zeta8`,
  `Vec n`, `applyOne`, `applyCNOT`, linearity, fusion, commutation;
  `applyOne_smul_one` (a scalar matrix on any wire scales the state) and
  `Gate1.S_mul_H_pow_three` (`(S H)³ = ω`), the leaves of the phase gadget.
- `CircuitEq/Dyadic.lean` — `Quantum.Dyadic8`, the gcd-free ring
  `ℤ[ω, 1/√2]` the decision procedure computes in: four `ℤ` coordinates and
  a `√2` exponent, `add` / `mul` / `eqv` by exponent alignment, `toZeta8`
  with a `toZeta8_*` lemma per operation and `eqv_iff`. The per-gate
  actions `Gate1.applyD` (on `Fin`, proved against `applyOne g.mat`) and
  `Gate1.applyN` / `applyCNOTN` (on `ℕ`, definitionally the same; what
  `evalFn` composes), plus the generic `Gate1.matD` / `applyOneD` mirror of
  `applyOne`. A computational device only: `denote` stays over `Zeta8`.
- `CircuitEq/Chunk.lean` — chunked kernel evaluation: `AllBelow P k`
  (`P y = true` for every `y < k`), `AllBelow.zero`, `AllBelow.add` (extend
  by a range `(List.range' lo len).all P = true`, itself one
  `decide +kernel`). The kernel keeps its reduction cache for a whole
  declaration, so a check over many indices is proved one range per
  declaration and assembled by a constant-size term; peak memory is one
  chunk's. Generated files must start with `set_option Elab.async false`,
  or the memory of one declaration is not returned before the next
  starts. Consumers: `equivalent_of_allBelow`,
  `equivalentUpToPhase_of_allBelow`, `equivalentWithPhase_of_allBelow`,
  `tableau_sound_of_allBelow`.
- `CircuitEq/Semantics.lean` — the trusted core, and nothing else:
  `Instr`, `Circuit n := List (Instr n)`, the readable constructors,
  `denote` with `denote_cons` / `_append` / `_add` / `_smul`, and the four
  relations: `Equivalent` (`≡ᵤ`), `EquivalentWithPhase k` (`a ≡ₚ[k] b`,
  `k : Fin 8`: `a` is `ω ^ k` times `b`), `EquivalentUpToPhase` (`≡ₚ`,
  defined as `∃ k, a ≡ₚ[k] b`) and `EquivalentUpToScalar` (`≡ₛ`, up to a
  unit of `Zeta8`; what a tableau certifies). A trust review reads this
  file; keep proofs out of it.
- `CircuitEq/Relations.lean` — the algebra of the relations. `≡ᵤ`:
  `@[refl]`, `@[symm]`, `@[trans]`, `append`, `cons`, `toWithPhase`,
  `toUpToPhase`, `toUpToScalar`. `EquivalentWithPhase.refl` (phase `0`),
  `symm` (`-k`), `trans` and `append` (`j + k`, modulo eight because it is
  `Fin 8`), `append_left` / `append_right` / `cons` / `trans_equivalent`
  (the phase is kept), `cast` (restate an exponent that arithmetic
  produced), `toUpToPhase`, `toEquivalent` and
  `equivalentWithPhase_zero_iff` (`≡ₚ[0]` is `≡ᵤ`); the `≡ₚ` lemmas are
  these with the exponent forgotten; `≡ₛ` has `refl`, `symm`, `trans`,
  `append`. `Trans` instances for every pair among `≡ᵤ`, `≡ₚ[k]` and
  `≡ₚ`, so one `calc` mixes them: exact steps keep a named phase, named
  phases add (a goal stated with the numeral closes by unification), and
  one `≡ₚ` step makes the chain `≡ₚ`.
- `CircuitEq/Decide.lean` — deciding concrete pairs: `denoteₗ`, basis
  reduction (`equivalent_iff_basis`, `equivalentWithPhase_iff_basis`), the
  evaluators `evalList` (reference, over `Zeta8`), `evalListD` (its dyadic
  form) and `evalFn` (dyadic closures on `ℕ` indices, what the instances
  run), `checkEquiv`, `checkEquivWithPhase a b k` and `checkEquivUpToPhase`
  (the first at each of the eight phases) with their `_iff` lemmas, the
  per-basis-vector chunks `checkEquivAt` / `checkEquivUpToPhaseAt` with
  `equivalent_of_allBelow`, `equivalentWithPhase_of_allBelow` and
  `equivalentUpToPhase_of_allBelow`, `findPhase` (`findPhase_sound`,
  `findPhase_isSome_iff`; the first of the eight phases that passes), and
  the `Decidable` instances for `≡ᵤ`, `≡ₚ[k]` (one phase, so
  `decide +kernel` names a window's phase and refutes a wrong one) and
  `≡ₚ`.
- `CircuitEq/Checker.lean` — the checker contract: `Checker n` is
  `check : Circuit n → Circuit n → Bool` plus `sound : check a b = true →
  a ≡ᵤ b` (`PhaseChecker`, `ScalarChecker` for `≡ₚ`, `≡ₛ`); `NormalForm n`
  with `toChecker`; `Checker.orElse`; `syntacticChecker`; `evalChecker`
  (the basis decide as a checker). Up to phase there are two contracts: a
  `PhaseChecker` answers `Bool` and proves `a ≡ₚ b` (`evalPhaseChecker`,
  `PhaseChecker.orElse`), a `PhaseFinder` answers `find a b : Option (Fin
  8)` and proves `a ≡ₚ[k] b`, which is what a certificate needs, because
  the phases of its windows have to be added up: `evalPhaseFinder` (the
  basis evaluator by `findPhase`), `Checker.toFinder` (an exact checker
  finds `0` or nothing), `PhaseFinder.orElse`, `PhaseFinder.toChecker`.
  A checker module imports only
  `Decide`, `Structural`, `Support` and `Checker`, writes `check` as
  kernel-friendly `Bool` code, and exports exactly one checker.
- `CircuitEq/Support.lean` — wire sets as `Nat` bitmasks, the one encoding
  every checker and the certificate language use: `Instr.support`,
  `support`, `masksDisjoint`, `support_testBit`,
  `not_touches_of_disjoint`; `Rewriting.lean` adds
  `Instr.CanCommute.of_disjoint` and `gate_block_comm_of_disjoint`. Do not
  invent a second encoding of wire sets.
- `CircuitEq/Lanes.lean` — the bit-plane arithmetic under the phase
  polynomial, nothing in it about circuits: `Lanes` (residues modulo 8 on
  many lanes as three `Nat` planes; `add`, `addOn`, `addOnz`, `lane`,
  `ext_of_lane`) and, all under `Lanes.`, the combinatorial numbering of
  pairs and triples (`tri`, `tet`) and the masks of the pairs and triples
  inside a parity (`pairMask`, `tripMask`, by `maskFold` over `bitFold` or
  `sparseFold`, with `popCount`, `lowBit`, `idx`).
- `CircuitEq/PhasePoly.lean` — the phase-polynomial canonical form for the
  CNOT-plus-diagonal fragment (`CX` and `Z, S, Sdg, T, Tdg`): `PhasePoly` is the
  `𝔽₂`-linear part as `rows`, one `Nat` holding `n` bitmasks of `n` bits
  (`row n R i`), and the phase function as its multilinear polynomial over
  `ℤ/8`, which has degree at most three and is unique: `deg1`, `deg2`,
  `deg3 : Lanes`, three bit planes each, the coefficient of `yᵢ` in lane `i`, of
  `yᵢ yⱼ` in lane `tri j + i` and of `yᵢ yⱼ yₗ` in lane `tet l + tri j + i`
  (`C(j,2)`, `C(l,3)`: the planes are exactly `C(n,2)` and `C(n,3)` bits). A
  CNOT is a shift and an xor; a phase gate of phase `k` on a parity `m` adds
  `k`, `−2k`, `4k` on the lanes of the wires, pairs and triples of `m`
  (`Lanes.addOn`, a ripple-carry adder on planes; `Lanes.pairMask`,
  `Lanes.tripMask`, one shift-and-or per set bit by `Lanes.maskFold`, which
  visits only the set bits of a sparse parity, lowest bit by `gcd`, index by a
  population count checked on 1024 powers of two, and tests every index of a
  dense one; `Lanes.addOnz` skips a plane with nothing to add). `nf`,
  `phasePolyNormalForm n`, `phasePolyChecker n`.
  `CircuitEq/PhasePoly/Complete.lean` has `PhasePoly.complete` (equal unitaries
  give equal forms) and so `phasePolyRefutes n a b`, whose `true` proves
  `¬ a ≡ᵤ b`, and `phasePolyChecker_check_iff`: within the fragment `check` is a
  decision procedure. Cost is linear in the gate count and never `2 ^ n`
  (seconds for thousands of gates on hundreds of wires; the figures are in
  `benchmarks/scale/README.md`); what grows is the `C(n,3)`-bit triple plane,
  copied by every gate that changes it (`QUEUE.md` item 8). A proof is
  `(phasePolyChecker n).sound _ _ (by decide +kernel)`, a refutation
  `phasePolyRefutes_sound (by decide +kernel)`; bare `decide` times out at about
  a hundred gates. The extension with Hadamard variables that certifies TZAP
  output across `H` gates is `QUEUE.md` item 4.
- `CircuitEq/Tableau.lean` — the Clifford tableau checker: `Pauli` strings
  (x-mask, z-mask, phase in `Fin 4`, denoting `i^p · Z^z · X^x`), the gate
  update rules with pointwise soundness (`conjH_sound`, …, `conjCX_sound`),
  `Tableau.conj` / `tableau` (images of the `2n` generators, `none` outside the
  fragment or for `CX c c`), `tableauCheck`, `tableau_sound` (equal tableaux
  give `≡ₛ`, the normal-form shape) and the export
  `tableauChecker n : ScalarChecker n`; `Tableau.witness` names the first
  disagreeing generator. The soundness argument is stated on
  `Tableau.ConjAgree a b` (every generator has the same image), so the chunked
  form shares it: `Tableau.genAt n g` numbers the `2n` generators on `ℕ`,
  `tableauCheckGen a b g` checks one, and `tableau_sound_of_allBelow` turns
  `AllBelow (tableauCheckGen a b) (2 * n)` into `a ≡ₛ b`. The API (`Pauli`,
  `tableau`, `tableauCheck`, `tableauChecker`, `tableauCheckGen` and the
  soundness theorems) is at the top of `Quantum.Circuit`; the helpers
  (`Tableau.phaseVal`, `sign`, `xorMask`, `generators`, `mapOpt`, the commutant
  argument) are under `Tableau.`, as the phase polynomial's are under
  `PhasePoly.` and `Lanes.`, so that checker internals do not crowd the
  library's namespace. Structure-independent, `O(n)` bit operations per gate, no
  `Zeta8` arithmetic in the kernel; the cost is `2n · gates` steps (per-step
  figures in `benchmarks/scale/README.md`), and past a few thousand gates the
  check must be chunked (`scripts/scale_test.py --chunk`). Extend `Gate1.conj`
  (with a `sound` case) if the Clifford alphabet grows.
- `CircuitEq/Structural.lean` — the parametric toolkit: fusion,
  commutation, `denote_applyOne_comm_of_not_touches`, `layer`, `hLayer`,
  and the phase gadget: `phaseGadget k i` is `k` rounds of `H S H S H S`
  on wire `i`, Clifford gates only, and denotes the scalar `ω ^ k` on every
  register (`denote_phaseGadget`; `phaseGadget_comm`, `phaseGadget_wire`,
  `phaseGadget_eight`, `phaseGadget_equivalentWithPhase`). The bridge
  `equivalentWithPhase_iff_phaseGadget : a ≡ₚ[k] b ↔ a ≡ᵤ b ++ phaseGadget
  k i` (and `equivalentUpToPhase_iff_phaseGadget` with `∃ k`) normalises a
  pair that is equal only up to a phase to an exact one at no `T`-cost.
- `CircuitEq/Rewriting.lean` — rewriting on instruction lists:
  `Equivalent.in_context` (and `EquivalentWithPhase.in_context`,
  `EquivalentUpToPhase.in_context`: a window's phase is the phase of the
  whole), the decidable checks `Instr.CanCommute` /
  `Instr.CanCancel` with their `sound` lemmas, `gate_block_comm`,
  `blocks_comm`, `perm_equivalent`, `pull_cons`, `cancel_window`.
  `CanCommute` licenses: equal gates, disjoint wires, two diagonal gates on
  one wire, a diagonal gate on a CNOT control, `X` on a CNOT target, CNOTs
  whose controls avoid each other's targets. Extend it there (with a
  `sound` case) when a benchmark needs a new local commutation; the
  tactics pick it up automatically.
- `CircuitEq/Layers.lean` — `cnotNetwork`, `swapEndpoints`, `hOn` (a layer
  indexed by a `Finset`), `hOn_symmDiff`, `cnotNetwork_layer`, and the
  benchmark-facing `layer_cnotNetwork_hLayer`.
- `CircuitEq/Certificate.lean` — the certificate language: `Step n` (`swap`,
  `moveLeft`, `moveRight`, `cancel`, `insert`, `window`), plain data with
  positions as `ℕ`; `replay Cs steps c : Option (Circuit n)`, a kernel-friendly
  interpreter that checks each step (`Instr.CanCommute`, `masksDisjoint` on
  supports, `Instr.CanCancel`, or checker `k` of the table `Cs : CheckerTable`
  on the window's own wires); `replay_sound`; the closing form
  `replay_sound Cs steps (by decide +kernel)` and the macro
  `circuit_replay Cs steps`. Generic in the table: it imports no checker, and no
  checker module imports it. A new proof technique is a new step kind here with
  its case in `replayStep_sound`; the kernel evaluates `replay` once per proof.
  The same `Step`s replay up to a global phase:
  `replayPhase Fs steps c : Option (Fin 8 × Circuit n)` reads a `window` against
  a `PhaseTable` of `PhaseFinder`s (`windowPhase`), places it syntactically
  (`placeFront`) and adds the exponent found to an accumulator; every other step
  is the exact rewrite.
  `replayPhase_sound : replayPhase Fs steps c = some (k, c') → c ≡ₚ[k] c'`, so
  the kernel computes the phase of the whole pair; `replayUpToPhase` /
  `replayUpToPhase_sound` forget it and conclude `c ≡ₚ c'`; the macro
  `circuit_replay_phase Fs steps`, which closes either goal. `rewriteAt_rel` is
  `rewriteAt_sound` for any relation that `cons` preserves, and a new step kind
  needs its case in `replayStepPhase_sound` too. The phase replay costs about
  1.2 times the exact one (`benchmarks/scale/README.md`, "Where each tool
  stands"). Measure with `set_option Elab.async false`: with asynchronous
  elaboration the kernel checks of neighbouring declarations overlap and the
  profiler's figures grow with position in the file. The scalar replay for `≡ₛ`
  (so that the tableau can justify a window) is still open (`QUEUE.md` item 13).
- `CircuitEq/Defaults.lean` — the tables the tactics replay under, and the
  one place a checker joins them: `defaultCheckers` (index 0:
  `phasePolyChecker` with `evalChecker` as fallback, so a
  CNOT-plus-diagonal window is decided symbolically and only otherwise by
  the basis; index 1: `syntacticChecker`) and `defaultPhaseFinders` (index
  0: `phasePolyChecker` lifted, then `evalPhaseFinder`; index 1:
  syntactic).
- `CircuitEq/Tactic.lean` — `circuit_simp` (cancel checked inverse pairs
  through commuting gates, then align two concrete lists gate by gate) and
  `circuit_windows [(a₁, b₁), …]` (the window pattern: each window is
  decided on its own wires by the checker table, every other move is a
  checked commutation, windows are consumed in the listed order). Both
  search in meta code and emit a `List (Step n)` closed by `replay_sound`,
  so the kernel evaluates `replay` once; moves found on the right-hand
  circuit are inverted into the same trace. Both read lists by `whnf`, so
  `layer`, `cnotNetwork`, `hLayer` and named circuit `def`s are fine as
  inputs. Neither searches for an alignment. Both accept a goal
  `a ≡ₚ b` or `a ≡ₚ[k] b` as well: the search and the trace are the same,
  the trace is replayed by `replayPhase` under `defaultPhaseFinders`, each
  window may hold only up to a phase of its own (`Z X` against `X Z`), and
  on `≡ₚ[k]` the windows' phases must add up to `k`. The errors say which
  case failed: a window the kernel refutes even up to phase, a named phase
  that is wrong (the message names the right one), or, on an exact goal, a
  window that holds only up to phase (the message says to state the goal
  on `≡ₚ`).
- `CircuitEq/Embedding.lean` — the locality theorem: `rename f c` places a
  circuit on the wires `f : Fin m ↪ Fin n`, `rename_equivalent_iff`,
  `Equivalent.rename`, `wires₁` / `wires₂` / `wires₃` for concrete
  embeddings. Up to a scalar the slicing argument is the same, so it is
  proved once for an arbitrary `s : Zeta8` (`denote_rename_eq_smul`,
  `denote_eq_smul_of_rename`) and specialised: `EquivalentWithPhase.rename`
  / `of_rename` / `rename_equivalentWithPhase_iff` (the phase is kept),
  `EquivalentUpToPhase.rename` / `of_rename` /
  `rename_equivalentUpToPhase_iff`, and `EquivalentUpToScalar.rename`.
- `CircuitEq/Examples.lean` — worked identities; add new showcase results
  here, new general lemmas to `Structural.lean`, `Rewriting.lean` or
  `Layers.lean`. Built through `CircuitEqTest.lean`, not the umbrella; the
  agent harness keeps it in a run's workspace, as the playbook's quickest
  way to see each tool used.
- `CircuitEqTest/PhasePoly.lean`, `CircuitEqTest/Tableau.lean` — the
  checkers' regression tests (completeness cases, fragment boundaries,
  refutations, chunked forms). Several restate parts of benchmark answers,
  so the harness removes `CircuitEqTest/` from every run's workspace; a
  test that shows how to use a tool belongs in `Examples.lean` instead.
- `CircuitEq/Benchmarks/*.lean` — one module per original-versus-PyZX pair,
  with QASM fixtures and provenance under `benchmarks/<name>/`. Keep each to
  the two circuit `def`s (which `scripts/check_pyzx_benchmarks.py` parses
  and compares with the QASM) and the equivalence theorem; development
  sanity checks (duplicate `decide` proofs, mutants) do not belong in the
  repo. The script knows two pipelines, `full_reduce` (re-synthesis) and
  `teleport` (phase teleportation, skeleton-preserving, the one that gives
  alignable T-count pairs), and translates `cz` to `H; CX; H` and
  `rz(k·π/4)` to the diagonal Clifford+T gate with that matrix. A `tzap`
  pipeline (https://github.com/qqq-wisc/tzap) for this script is queued
  (`QUEUE.md` item 5); `scripts/circuit_pairs.py` already runs TZAP as a twin
  kind. TZAP reads and writes the same `rz` convention as PyZX.
- `scripts/scale_test.py` — the scale ladder (`benchmarks/scale/`): seeded
  families (`clifford`, `cnot_t` random; `ghz`, `surface`, `ccz_net`
  structured), PyZX pipelines including the peephole `basic`, `--chunk G`
  for the chunked tableau, and a Python mirror of the Pauli update rules
  that pre-checks a pair and names a mutant's witness generator.
  `scripts/chunked_decide.py <Module>` emits and times the chunked basis
  decide of a benchmark module; `scripts/chunks.py` is what both share.
- `PLAYBOOK.md` — the prover's guide: what exists, what it costs, and in
  which order to try it on a concrete pair. The agent harness installs it
  as the `CLAUDE.md` of every run (`benchmarks/harness/PLAYBOOK.core.md`
  for the `core` configuration, the modules up to `Decide.lean`), so it
  is all an agent under test knows about the library. **When a checker, a
  tactic, a certificate step or a block theorem lands, update its decision
  list in the same commit** (both playbooks if the module is in
  `CORE_MODULES`), and the commit named at its top.
- `scripts/agent_harness.py`, `scripts/optimizer_harness.py`,
  `benchmarks/harness/` — the agent harnesses (`benchmarks/harness/README.md`).
  The equivalence one: a fixed prompt (`PROMPT.md`), tasks as circuit pairs
  under `tasks/`, a warm clone of a library commit with the answer held out,
  a budget, a memory watchdog, and a judge that restates the claim, checks
  its axioms and replays the solution through the kernel (`leanchecker`).
  The optimiser one is built on the same pieces (`PROMPT.optimize.md`,
  `opt-tasks/`, a cost measured in Lean, the best accepted submission
  judged in a fresh clone). `tools/qasm.py` is the exact Lean-to-QASM
  converter every run gets as `./qasm`; `notes/` holds measurements;
  `results/` keeps each recorded run's solution, `changes.diff` and
  `judge.json`, with a row in `results.jsonl` that a person marks
  `reviewed` after reading the diff. Both refuse to run lake where mathlib
  is not already compiled. Changing a prompt, the judge or the agent
  configuration changes the instrument: bump `HARNESS_VERSION` or
  `OPT_HARNESS_VERSION`. No Lean under `benchmarks/` is in a `lean_lib`:
  CI never builds it, only the text guard scans it.
- `benchmarks/circuits/`, `scripts/circuit_sources.py`,
  `scripts/circuit_pairs.py`, `scripts/peephole_pairs.py` — the circuit
  catalogue (`benchmarks/circuits/README.md`): 147 real Clifford+T circuits
  (the Feynman suite, QASMBench, TZAP's corpora, QECUnitaryCircuits and
  parametric generators) in four tiers, fetched at pinned commits into
  `~/.circuiteq-harness/circuit-cache` and translated into the alphabet
  exactly or refused with the reason: no rotation is approximated, every
  translation is checked numerically with the global phase, and
  `manifest.json` holds every hash. `circuit_pairs.py` makes twins (the
  peephole pass, PyZX's two pipelines, TZAP, and the Nam et al., T-par and
  PyZX outputs published for the Feynman suite), records the relation that
  actually holds and each pair's diff and segmentation (`pairs/index.json`),
  and writes `optimization.json`, the uncertified T-counts per circuit.
  **The licence rule:** a pair whose twin comes from a source without a
  clear licence (Nam et al., T-par) lives in the cache only, never in the
  repository. `peephole_pairs.py` draws seeded random pairs equal by the
  library's own rules. CI runs the self-tests of `circuit_sources.py`,
  `circuit_pairs.py` and both harnesses.
- `scripts/alphabet.py` — the gate alphabet once for every script: `GATES`,
  `DIAG`, the fragments, `INVERSE`, `PHASE_OF_GATE` / `PHASES` (`diag(1,
  ω^k)` as gates), the QASM names and the matrices. Standard library only;
  `--self-test` (CI) checks it against `Gate1` and `Gate1.phase?` in the Lean
  sources and against the copy `benchmarks/harness/tools/qasm.py` keeps
  (that file is installed alone in a run workspace). A script that needs a
  gate table imports it from here.
- `scripts/certificate.py` — the Python mirror of the certificate language
  (`replay`, `replay_phase`, `align`, `fmt_certificate`), so a search
  outside Lean emits traces `replay` accepts; `--phase` certifies up to a
  phase and names it, `--theorem` prints the Lean. `scripts/tcount_survey.py`
  — the T-count survey (`benchmarks/survey/`), its diff-based alignment
  search and a numpy comparison of unitaries.
- `scripts/AxiomCheck.lean` — CI axiom policy; not in any `lean_lib`.
- `scripts/check_debug_options.py`, `scripts/SkipKernelTCFixture.lean`,
  `scripts/check_replay_fixture.sh` — the kernel-replay policy's text guard
  (an early warning, not sound), its regression fixture (`2 + 2 = 5` behind
  `debug.skipKernelTC`; not in any `lean_lib`, never imported, the one file
  the guard exempts) and the CI assertion that the fixture compiles clean,
  is flagged by the guard and is rejected by `leanchecker`. See
  "Conventions".

Namespaces: `Quantum.Zeta8` for the field, `Quantum.Circuit` for everything
else (the type `Quantum.Circuit n` lives at the namespace's own name, like
`List`). Readable instruction constructors live in `Quantum.Circuit.Instr`
(`H i`, `T i`, `CX c t`, …); `open Quantum.Circuit Instr` in example files.

## Conventions

- **Measurements are recorded once.** A kernel time, a memory peak or a
  scale limit goes, dated and with the command that reproduces it, into
  `benchmarks/scale/README.md` (the checkers, the evaluator, replay) or the
  benchmark's own `benchmarks/<name>/README.md`. Every other living document,
  this file, `README.md`, the Lean docstrings, states the conclusion (linear
  in gates, bounded by memory at seven qubits) and links there. Two
  exceptions: `PLAYBOOK.md` and `benchmarks/harness/PLAYBOOK.core.md` are
  all an agent under test sees, so they carry the numbers they need; when
  the scale README changes, update them in the same commit. `QUEUE.md`
  "Done" entries and the dated status paragraphs of `ROADMAP.md` are records
  of their date and are not rewritten.
- **Lemmas** `snake_case`, **definitions** `camelCase`, `theorem` for
  results, `lemma` for stepping stones. Docstrings on every declaration.
- **`decide +kernel`, never bare `decide`, for anything touching `Zeta8`.**
  `Rat.add`/`Rat.mul` are `@[irreducible]`, so elaborator-level `decide`
  reports "reduction got stuck" on the first rational addition. The kernel
  ignores reducibility hints. Bare `decide` is fine for pure `Nat`/`Bool`/
  `Fin` facts (the bit lemmas).
- **`native_decide` is banned.** It adds a compiler-trust axiom. CI runs
  `lake env lean scripts/AxiomCheck.lean` and fails on anything beyond
  `[propext, Classical.choice, Quot.sound]`. Check a result with
  `#print axioms`. `sorry` only on WIP branches, tagged
  `sorry -- TODO(<tag>): <goal shape>`.
- **`debug.*` options are banned, and the kernel replay is the other half of the
  trust policy.** `set_option debug.skipKernelTC true` makes Lean add a
  declaration without sending it to the kernel. `decide +kernel` leaves its
  whole check to the kernel, so under the option a false leaf proof elaborates
  without an error and the axiom check reports it clean: it depends on no axioms
  at all (verified on this toolchain, 18 September 2026: `2 + 2 = 5`, and `[H 0]
  ≡ᵤ [X 0]` inside a library module, with `lake build` and `AxiomCheck` both
  green). So CI also replays every declaration of the built `.olean` files
  through the kernel, `LEAN_NUM_THREADS=1 lake env leanchecker CircuitEq
  CircuitEqTest`, in a process where no option or meta code of the library runs.
  `leanchecker` is the former lean4checker, shipped inside the toolchain since
  v4.28 (the separate repository is deprecated and has no tag for this
  toolchain), so it always matches `lean-toolchain`.
  `scripts/check_replay_fixture.sh` asserts on every CI run that the replay
  rejects the repro kept in `scripts/SkipKernelTCFixture.lean`.
  `scripts/check_debug_options.py` is a text guard for the obvious spellings in
  the Lean sources and `lakefile.toml`; it is an early warning and is not sound,
  because an option can be set from meta code under a name no search recognises
  (a variant that assembles the name from string pieces passes the guard and the
  axiom check, and the replay rejects it). The replay is the defence. It
  re-checks this library's modules against their imports as delivered: mathlib
  and core are trusted as the cache provides them, and it is the same kernel
  again, not an independent checker. Never set a `debug.*` option in the
  library, in `scripts/` or in `lakefile.toml`; a proof that needs one is not a
  proof.
- **No `set_option linter.* false`.** Fix the warning or leave it visible.
  The build is currently warning-free; keep it that way.
- **Docstring prose wraps at 80 columns**, code at 100 (the `longLine`
  linter only fails at 100, the 80 is house style). Fenced code blocks may
  exceed 80 if they must.
- **Notation.** `≡ᵤ` and `≡ₚ` are `scoped infix` in `Quantum.Circuit`, and
  `a ≡ₚ[k] b` is `EquivalentWithPhase k a b`. `≡ₚ[` is a token of its own,
  so keep the space in `a ≡ₚ [X 0]`: without it the list is read as a
  phase. Do not use `≈`: on `List` it already means `List.Perm`. Ascribe
  one side of a concrete equivalence with `: Circuit n`; the qubit count is
  not inferable from `[H 0, T 0]`.
- **Hand-written algebraic instances** on this mathlib (v4.30.0-rc2) must
  supply `nsmul := nsmulRec` and `zsmul := zsmulRec` explicitly in a
  `CommRing`; there is no default.
- **Circuits are lists in time order.** `denote [g₁, g₂] ψ = U₂ (U₁ ψ)`;
  fusion lemmas therefore have the *later* gate as the left matrix factor
  (`fuse : B.mat * A.mat = C.mat → [one A i, one B i] ≡ᵤ [one C i]`).
- **Benchmark proofs are `calc` chains on lists.** Name the block
  decomposition (`layer`, `cnotNetwork`, `hLayer`, a `def edges`), equate
  the circuit to it by `rfl`, apply the block theorem, and finish with
  `circuit_simp`. Do not unfold `denote` and rewrite with `applyOne_comm`
  gate by gate; that is what `CircuitEq/Rewriting.lean` exists to avoid.
  `perm_equivalent` needs *every* pair in the block to commute; when only
  the moved gates need to, use `circuit_simp` or `pull_cons`. When the
  optimiser rewrote a few local regions, hand them to `circuit_windows` as
  `(before, after)` pairs rather than writing `in_context`, `rename` and
  `decide +kernel` by hand; a window's decide costs `2 ^ k` for its `k`
  wires, not `2 ^ n`.
- **A pair that is equal only up to a global phase is stated on `≡ₚ`**, and
  proved with the same tools: `circuit_windows` on the `≡ₚ` goal, `calc`
  chains that mix `≡ᵤ` and `≡ₚ` steps, `append` and `in_context` for
  segments. PyZX and TZAP drop scalars, so expect this of their output.
  State `≡ₚ[k]` when the phase matters (the error names the right `k` if
  yours is wrong), and use `equivalentWithPhase_iff_phaseGadget` to turn it
  into an exact statement against `optimized ++ phaseGadget k i`. Never
  decide a phase on the whole register when a window can carry it.

## Build and verification

```bash
lake build                            # library, examples, tests (~1 min warm)
lake env lean scripts/AxiomCheck.lean # axiom policy, needs a completed build
LEAN_NUM_THREADS=1 lake env leanchecker CircuitEq CircuitEqTest  # kernel replay
bash scripts/check_replay_fixture.sh  # the replay still rejects the repro
python3 scripts/check_debug_options.py  # text guard, needs no build
lake env lean /tmp/probe.lean         # one-off file check
```

Always `lake build` before claiming a fix works; the error output prints the
residual goal under each failure.

**The kernel replay runs on one thread.** (Not the certificate `replay` of
`Certificate.lean`: this is `leanchecker` over the `.olean` files.) It
replays modules in parallel, and every replay beyond the first loads a
private copy of the mathlib imports. Measured on the M4 (18 and 19
September 2026; 23 modules, 2119 declarations): one thread 22 to 28 s,
0.33 to 0.41 GB peak footprint (1.7 to 1.8 GB resident, almost all of it
the mapped mathlib `.olean` files); two threads 16 s and 2.1 GB; the
default ten threads were killed by the OS after 4 minutes at a 26 GB
footprint. On GitHub's `ubuntu-latest` runner the one-thread replay is a
25 to 39 s step in a 2 to 3 minute job, and the fixture check 2 s. It is a CI
step of its own, not lean-action's `leanchecker` input, because the thread
cap would sit on that whole step and slow the build too; `-v` makes the
log list the modules replayed. Never run it without `LEAN_NUM_THREADS=1`,
and count it as a lake process for the rule below. It replays whatever
`.olean` files are under `.lake/build`, so delete the build products of a
module you remove (`lake build` does not) or the replay keeps checking the
stale file.

**Sharing mathlib with QECLean.** This project pins the same mathlib commit
as the sibling repo `../QECLean`. `.lake/packages` may be a symlink to
`../QECLean/.lake/packages` so mathlib is never downloaded or rebuilt here;
only immutable dependency artifacts are shared and this project's own
`.lake/build` stays separate. If the two manifests ever differ, do **not**
symlink: use `lake exe cache get` (ask first, see below).

**Never run these without asking the user first:** `lake exe cache get`,
`lake update`, anything that re-downloads or rebuilds mathlib. They take
minutes to hours and hold the workspace lock. **Never run two lake processes
concurrently** (this includes the lean-lsp MCP server, which shares the lock
with `lake build`).

## Agent tooling: lean-lsp MCP

`.mcp.json` ships the `lean-lsp-mcp` server. It is the default interface to
the compiler while iterating; `lake build` is the commit-time confirmation.

- `lean_diagnostic_messages` with `severity: error` to localise; read the
  first error first.
- `lean_goal` for the proof state at a position.
- `lean_multi_attempt` when there are 3+ candidate tactics.
- `lean_local_search` before guessing a lemma name; the external search
  tools rate-limit.
- `lean_verify` (fully qualified name) for the axiom check of one theorem.
- `lean_run_code` for a self-contained probe; the LSP builds project imports
  on demand.

Do not run `lake build` between diagnostics edits; one build at the end.

## Kernel-cost notes

The `Decidable` instances for `≡ᵤ`, `≡ₚ` and `≡ₚ[k]` run `checkEquiv`,
`checkEquivUpToPhase` and `checkEquivWithPhase` (`Decide.lean`): the closure
evaluator `evalFn` over `Dyadic8` (`Dyadic.lean`), the gcd-free ring
`ℤ[ω, 1/√2]`, on `ℕ`-indexed states, proved equal to `denote`
(`toZeta8_evalFn`). The kernel memoises `whnf` by structural term equality, so a
depth-`d` decide on `k` qubits costs `d · 2^k` memoised gate steps, each a
coordinate shuffle or, for `H`, four integer sums, plus `4^k` final comparisons;
the kernel never sees a rational and never walks a list. Never `decide` through
`denote` directly: its closures are over `Fin`, whose indices carry proof terms
that defeat the cache, so it re-reads the input `2^d` times.

A whole-register decide therefore costs `gates · 4^n` memoised amplitude
steps, about 150 µs and 40 KB each, and the kernel retains all of them until
the declaration ends: memory runs out before time does, a seven-qubit pair
needs chunked evaluation (`CircuitEq/Chunk.lean`), eight qubits take minutes
and ten over an hour. Chunked files need `set_option Elab.async false`, or
the memory of one declaration is not returned before the next starts
(`lean -j1` does not help). The measurements behind these figures, and the
designs measured on the way, are in `benchmarks/scale/README.md`, "The basis
evaluator".

Kernel facts measured while scaling the fragment checkers
(`benchmarks/scale/README.md`): a step of structural recursion with a few
`Nat` operations costs 150 to 200 µs and retains 10 to 40 KB;
`List.set` / `List.getD` on an 80-element list retain about 1.5 MB per
update (pack tables into one `Nat`); `Nat.log2` is *not* accelerated
(`Nat.add, sub, mul, div, mod, gcd, beq, ble, land, lor, xor, shiftLeft,
shiftRight, pow` are); a loop that returns its accumulator unchanged
should return the same term, not `0 ||| acc`, which allocates a fresh
literal; a `def` of a list literal beyond about a thousand elements needs
`set_option maxRecDepth` for the code generator. And the trap behind that
advice: a value that *every* step reads must be a literal at every step.
`whnf` follows a chain of pass-through terms (`if c then x else …`
returning `x`, a structure field copied by `{ s with … }`) without
consulting its cache, so reading it at each of `k` steps costs `k²` (a
field passed through 4000 steps: 0.8 s, forced by `||| 0`: 0.05 s; doing
it to the planes inside `Lanes.add` turned a 3 s check into minutes).
Pass-through is fine for a value read rarely, which is why
`Lanes.addOnz` skips at the gate level only.

`Finset.sum` unfolding in the kernel is slow. `Gate1.mat` products are over
`Bool` (a two-term sum) and are fine; do not introduce `Matrix (Fin (2 ^ n))`
products anywhere the kernel must evaluate.
