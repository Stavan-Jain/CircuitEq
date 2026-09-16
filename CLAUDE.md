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

- `CircuitEq.lean` — umbrella; every module must be imported here or it is
  never built, never linted, and its errors are invisible.
- `CircuitEq/Zeta8.lean` — `Quantum.Zeta8`, computable ℚ(ζ₈). Constants
  `ω`, `I`, `sqrt2`, `invSqrt2`; identities by `decide +kernel`.
- `CircuitEq/Bits.lean` — `bit`, `flipBit` on `Fin (2 ^ n)`; the four lemmas
  `bit_flipBit_self`, `bit_flipBit_of_ne`, `flipBit_flipBit_self`,
  `flipBit_comm` are what every commutation proof rewrites with.
- `CircuitEq/Gates.lean` — `Gate1`, `Gate1.mat : Matrix Bool Bool Zeta8`,
  `Vec n`, `applyOne`, `applyCNOT`, linearity, fusion, commutation.
- `CircuitEq/Dyadic.lean` — `Quantum.Dyadic8`, the gcd-free ring
  `ℤ[ω, 1/√2]` the decision procedure computes in: four `ℤ` coordinates and
  a `√2` exponent, `add` / `mul` / `eqv` by exponent alignment, `toZeta8`
  with a `toZeta8_*` lemma per operation and `eqv_iff`. The per-gate
  actions `Gate1.applyD` (on `Fin`, proved against `applyOne g.mat`) and
  `Gate1.applyN` / `applyCNOTN` (on `ℕ`, definitionally the same; what
  `evalFn` composes), plus the generic `Gate1.matD` / `applyOneD` mirror of
  `applyOne`. A computational device only: `denote` stays over `Zeta8`.
- `CircuitEq/Semantics.lean` — `Instr`, `Circuit n := List (Instr n)`,
  `denote`, `denoteₗ`, `Equivalent` (`≡ᵤ`), `EquivalentUpToPhase` (`≡ₚ`),
  `EquivalentUpToScalar` (`≡ₛ`, up to a unit of `Zeta8`; what a tableau
  certifies), basis reduction, the evaluators `evalList` (reference, over
  `Zeta8`), `evalListD` (its dyadic form) and `evalFn` (dyadic closures on
  `ℕ` indices, what the instances run), `checkEquiv` /
  `checkEquivUpToPhase`, `Decidable` instances, `Trans` instance for
  `calc`.
- `CircuitEq/Checker.lean` — the checker contract: `Checker n` is
  `check : Circuit n → Circuit n → Bool` plus `sound : check a b = true →
  a ≡ᵤ b` (`PhaseChecker`, `ScalarChecker` for `≡ₚ`, `≡ₛ`); `NormalForm n`
  with `toChecker`; `Checker.orElse`; `syntacticChecker`; `evalChecker`
  (the basis decide as a checker). A checker module imports only
  `Semantics`, `Structural`, `Support` and `Checker`, writes `check` as
  kernel-friendly `Bool` code, and exports exactly one checker.
- `CircuitEq/Support.lean` — wire sets as `Nat` bitmasks, the one encoding
  every checker and the certificate language use: `Instr.support`,
  `support`, `masksDisjoint`, `support_testBit`,
  `not_touches_of_disjoint`; `Rewriting.lean` adds
  `Instr.CanCommute.of_disjoint` and `gate_block_comm_of_disjoint`. Do not
  invent a second encoding of wire sets.
- `CircuitEq/PhasePoly.lean` — the phase-polynomial normal form for the
  CNOT-plus-diagonal fragment (`CX` and `Z, S, Sdg, T, Tdg`): `PhasePoly`
  (one row bitmask per wire for the 𝔽₂-linear part, a sorted `(mask, phase)`
  list with `phase : Fin 8` for the phases), `PhasePoly.nf`,
  `phasePolyNormalForm n` and `phasePolyChecker n`. Cost is linear in the
  gate count and never `2 ^ n` (a 100-gate pair on ten wires is 0.2 s of
  kernel time); it decides T-count windows on many wires. A proof is
  `(phasePolyChecker n).sound _ _ (by decide +kernel)`; bare `decide` times
  out at about a hundred gates. It is the deterministic counterpart of
  TZAP's randomised parity analysis; the extension with Hadamard
  variables that certifies TZAP output across `H` gates is `QUEUE.md`
  item 2.
- `CircuitEq/Tableau.lean` — the Clifford tableau checker: `Pauli` strings
  (x-mask, z-mask, phase in `Fin 4`, denoting `i^p · Z^z · X^x`), the
  gate update rules with pointwise soundness (`conjH_sound`, …,
  `conjCX_sound`), `conj` / `tableau` (images of the `2n` generators,
  `none` outside the fragment or for `CX c c`), `tableauCheck`,
  `tableau_sound` (equal tableaux give `≡ₛ`, the normal-form shape) and
  the export `tableauChecker n : ScalarChecker n`; `witness` names the
  first disagreeing generator. Structure-independent, `O(n)` bit
  operations per gate, no `Zeta8` arithmetic in the kernel: the 15-qubit
  Reed–Muller pair decides in about 0.3 s. Extend `Gate1.conj` (with a
  `sound` case) if the Clifford alphabet grows.
- `CircuitEq/Structural.lean` — the parametric toolkit: fusion,
  commutation, `denote_applyOne_comm_of_not_touches`, `layer`, `hLayer`.
- `CircuitEq/Rewriting.lean` — rewriting on instruction lists:
  `Equivalent.in_context`, the decidable checks `Instr.CanCommute` /
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
- `CircuitEq/Certificate.lean` — the certificate language: `Step n`
  (`swap`, `moveLeft`, `moveRight`, `cancel`, `insert`, `window`), plain
  data with positions as `ℕ`; `replay Cs steps c : Option (Circuit n)`, a
  kernel-friendly interpreter that checks each step (`Instr.CanCommute`,
  `masksDisjoint` on supports, `Instr.CanCancel`, or checker `k` of the
  table `Cs : CheckerTable` on the window's own wires); `replay_sound`;
  `defaultCheckers` (index 0: `phasePolyChecker` with `evalChecker` as
  fallback, so a CNOT-plus-diagonal window is decided symbolically and
  only otherwise by the basis; index 1: `syntacticChecker`);
  the closing form `replay_sound Cs steps (by decide +kernel)` and the
  macro `circuit_replay Cs steps`. Never imported by a checker module. A
  new proof technique is a new step kind here with its case in
  `replayStep_sound`; the kernel evaluates `replay` once per proof.
- `CircuitEq/Tactic.lean` — `circuit_simp` (cancel checked inverse pairs
  through commuting gates, then align two concrete lists gate by gate) and
  `circuit_windows [(a₁, b₁), …]` (the window pattern: each window is
  decided on its own wires by the checker table, every other move is a
  checked commutation, windows are consumed in the listed order). Both
  search in meta code and emit a `List (Step n)` closed by `replay_sound`,
  so the kernel evaluates `replay` once; moves found on the right-hand
  circuit are inverted into the same trace. Both read lists by `whnf`, so
  `layer`, `cnotNetwork`, `hLayer` and named circuit `def`s are fine as
  inputs. Neither searches for an alignment.
- `CircuitEq/Embedding.lean` — the locality theorem: `rename f c` places a
  circuit on the wires `f : Fin m ↪ Fin n`, `rename_equivalent_iff`,
  `Equivalent.rename`, `wires₂` / `wires₃` for concrete embeddings.
- `CircuitEq/Examples.lean` — worked identities; add new showcase results
  here, new general lemmas to `Structural.lean`, `Rewriting.lean` or
  `Layers.lean`.
- `CircuitEq/Benchmarks/*.lean` — one module per original-versus-PyZX pair,
  with QASM fixtures and provenance under `benchmarks/<name>/`. Keep each to
  the two circuit `def`s (which `scripts/check_pyzx_benchmarks.py` parses
  and compares with the QASM) and the equivalence theorem; development
  sanity checks (duplicate `decide` proofs, mutants) do not belong in the
  repo. The script knows two pipelines, `full_reduce` (re-synthesis) and
  `teleport` (phase teleportation, skeleton-preserving, the one that gives
  alignable T-count pairs), and translates `cz` to `H; CX; H` and
  `rz(k·π/4)` to the diagonal Clifford+T gate with that matrix. A `tzap`
  pipeline (https://github.com/qqq-wisc/tzap) is queued; TZAP reads and
  writes the same `rz` convention as PyZX.
- `scripts/AxiomCheck.lean` — CI axiom policy; not in any `lean_lib`.

Namespaces: `Quantum.Zeta8` for the field, `Quantum.Circuit` for everything
else (the type `Quantum.Circuit n` lives at the namespace's own name, like
`List`). Readable instruction constructors live in `Quantum.Circuit.Instr`
(`H i`, `T i`, `CX c t`, …); `open Quantum.Circuit Instr` in example files.

## Conventions

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
- **No `set_option linter.* false`.** Fix the warning or leave it visible.
  The build is currently warning-free; keep it that way.
- **Docstring prose wraps at 80 columns**, code at 100 (the `longLine`
  linter only fails at 100, the 80 is house style). Fenced code blocks may
  exceed 80 if they must.
- **Notation.** `≡ᵤ` and `≡ₚ` are `scoped infix` in `Quantum.Circuit`. Do not
  use `≈`: on `List` it already means `List.Perm`. Ascribe one side of a
  concrete equivalence with `: Circuit n`; the qubit count is not inferable
  from `[H 0, T 0]`.
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

## Build and verification

```bash
lake build                            # whole library (~1 min warm)
lake env lean scripts/AxiomCheck.lean # axiom policy, needs a completed build
lake env lean /tmp/probe.lean         # one-off file check
```

Always `lake build` before claiming a fix works; the error output prints the
residual goal under each failure.

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

The `Decidable` instances for `≡ᵤ` and `≡ₚ` run `checkEquiv` and
`checkEquivUpToPhase` (`Semantics.lean`): the closure evaluator `evalFn`
over `Dyadic8` (`Dyadic.lean`), the gcd-free ring `ℤ[ω, 1/√2]`, on
`ℕ`-indexed states, proved equal to `denote` (`toZeta8_evalFn`). The kernel
memoises `whnf` by structural term equality, so a depth-`d` decide on `k`
qubits costs `d · 2^k` memoised gate steps, each a coordinate shuffle or,
for `H`, four integer sums, plus `4^k` final comparisons; the kernel never
sees a rational and never walks a list. Never `decide` through `denote`
directly: its closures are over `Fin`, whose indices carry proof terms that
defeat the cache, so it re-reads the input `2^d` times.

Measured on an Apple M4 (16 GB, shared with other builds), warm oleans,
kernel type-checking time of the `decide`, before → after: a two-qubit
five-gate window 0.35 s → 0.02 s; the three-qubit six-gate `Tof3` window
2.66 s → 0.09 s. Whole files, wall time: `Examples.lean` 2.6 s → 1.2 s and
`Tof3.lean` 4.2 s → 1.3 s, both now dominated by import time. The
seven-qubit `SteanePlus` pair decided on the full basis (`original ≡ᵤ
optimized` by `decide +kernel`, 32 gates × 128 basis states) is not
measured: it is memory-bound on this 16 GB machine, both before and after.
With the `Zeta8` `evalList` it did not finish in 15 minutes (71 s of CPU
against 248 s of system time, 15.8 GB peak footprint; the estimate for its
compute alone is 2 × 10⁵ Hadamard amplitude updates at some 10³ `Rat`
operations each, hours of kernel time). With the closure evaluator,
attempts of 9 and 3 minutes were stopped swap-starved (the 9-minute one
before reads were forced: 2:22 of CPU, 9.9 GB resident; see `Dyadic.lean`
on forcing). The expected cost is 5 × 10⁵ memoised gate steps and a cache
of the order of 10⁷ terms, tens of seconds and a few GB. Measured on an
idle machine (16 September 2026): a 6 GB watchdog killed the kernel after
20 s at 6.9 GB resident and still growing, 19 s of CPU. The cache, not the
arithmetic, is the wall; chunked evaluation (one lemma per basis vector or
per gate block, composed by `equivalent_iff_basis` or `Equivalent.trans`)
is the lever, and the same retention limits certificate replay
(`QUEUE.md`, item 1).

Two intermediate designs were measured on the way: the same dyadic
arithmetic through the materialised list evaluator (`evalListD`, kept as
the reference form) with the generic per-entry product (`applyOneD`) took
0.66 s on the three-qubit window and could not do seven qubits either,
because reading amplitude `x` of a list costs `x` steps and the kernel
retains every intermediate term (`O(4^k)` per gate, so memory runs out
before time does); the per-gate shuffles and the memoised closures with
forced reads bring it to 0.1 s. Depth is now linear: eighteen Hadamards on
one qubit decide in 42 ms, where the unforced closures did not finish in a
minute. Memory is the limit before time: the kernel's `whnf` cache retains
everything evaluated during one declaration.

`Finset.sum` unfolding in the kernel is slow. `Gate1.mat` products are over
`Bool` (a two-term sum) and are fine; do not introduce `Matrix (Fin (2 ^ n))`
products anywhere the kernel must evaluate.
