# CLAUDE.md — agent orientation

CircuitEq is a Lean 4 / mathlib library for stating and proving unitary
equivalence of Clifford+T quantum circuits. Read `README.md` first for the
pitch and the design; this file is the working conventions. Build with
`lake build`.

## What we are optimising for

The long-run goal is **agent-found structural proofs**: equivalences that
hold for every qubit count `n`, assembled from the toolkit in
`CircuitEq/Structural.lean` with `2 × 2` matrix facts as leaves. `decide
+kernel` on the computational basis is the oracle for concrete leaves and
small instances; it is not the plan for large circuits. When adding to the
library, prefer a lemma stated on `≡ᵤ` for arbitrary `n` over a bigger
`decide`.

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
- `CircuitEq/Semantics.lean` — `Instr`, `Circuit n := List (Instr n)`,
  `denote`, `denoteₗ`, `Equivalent` (`≡ᵤ`), `EquivalentUpToPhase` (`≡ₚ`),
  basis reduction, `Decidable` instances, `Trans` instance for `calc`.
- `CircuitEq/Structural.lean` — the parametric toolkit.
- `CircuitEq/Examples.lean` — worked identities; add new showcase results
  here, new general lemmas to `Structural.lean`.
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

`denote` on nested closures re-reads `ψ` at each flipped index, so a
depth-`d` concrete circuit costs up to `2^d` amplitude reads per output
entry (fine to depth ≈ 10 at `n ≤ 3`; the whole `Examples.lean` elaborates in
under ten seconds). The fix is roadmap item 1 in the README: a materialised
`List`-backed evaluator with a proven correspondence to `denote`. Until then,
do not add deep concrete `decide` examples; add structural lemmas instead.

`Finset.sum` unfolding in the kernel is slow. `Gate1.mat` products are over
`Bool` (a two-term sum) and are fine; do not introduce `Matrix (Fin (2 ^ n))`
products anywhere the kernel must evaluate.
