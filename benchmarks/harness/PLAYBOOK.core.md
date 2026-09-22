# The library, semantics only

This is the `core` configuration of the agent harness: the definitions that
say what a circuit means, and none of the infrastructure built on them. It is
the control arm; the difference between a run here and a run on the full
library is what the infrastructure is worth. Everything else you need you may
build yourself, in `Solution.lean` and new modules under `Solution/`.

## The objects

- A circuit on `n` qubits is `Quantum.Circuit n`, a list of instructions in
  time order: `[g₁, g₂]` applies `g₁` first. Gates are `H X Y Z S Sdg T Tdg`
  on a wire and `CX c t`; wires are `Fin n` literals.
- Write Lean inside `namespace Quantum.Circuit.<Name>` with `open Instr`, as
  `Solution.lean` does. Ascribe one side of a literal equivalence,
  `([H 0, H 0] : Circuit 1) ≡ᵤ []`.
- `CircuitEq/Semantics.lean` defines `denote : Circuit n → Vec n → Vec n`
  over the computable field `ℚ(ζ₈)` (`CircuitEq/Zeta8.lean`) and four
  relations: `a ≡ᵤ b` (`Equivalent`, equal on every state; it has `refl`,
  `symm`, `trans`, `append`, `cons`, and `calc` works), `a ≡ₚ b` (equal up to
  a power of `ω = e^{iπ/4}`; the same algebra, and `calc` mixes it with
  `≡ᵤ`), `a ≡ₚ[k] b` (the same with the phase named, `a = ω^k · b`, `k : Fin
  8`; phases add under `append`; keep the space in `a ≡ₚ [X 0]`, since
  `≡ₚ[` is its own token) and `a ≡ₛ b` (equal up to a nonzero scalar;
  it has `refl`, `symm`, `trans`, `append`).
- `CircuitEq/Gates.lean` has the gate matrices and the state-vector actions
  `applyOne`, `applyCNOT` with their linearity, fusion and commutation lemmas
  (`applyOne_applyOne_same`, `applyOne_comm`, `applyOne_applyCNOT_comm`,
  `applyCNOT_comm`, `applyCNOT_applyCNOT_self`, …) and the matrix identities
  (`H_mul_H`, `T_mul_T`, `S_mul_Sdg`, …). `CircuitEq/Bits.lean` has the four
  bit lemmas every commutation proof rewrites with.

## What decides a pair here

`≡ᵤ`, `≡ₚ` and `≡ₚ[k]` are `Decidable` for concrete circuits: every
instruction is linear, so equivalence reduces to the `2^n` basis vectors
(`equivalent_iff_basis`), and the instance evaluates both circuits with an
evaluator over the gcd-free ring of `CircuitEq/Dyadic.lean` that is proved
equal to `denote`. So `by decide +kernel` proves or refutes a small pair.

- Always `decide +kernel`. Bare `decide` stalls on the first rational
  addition, and `native_decide` is banned.
- The cost is `gates · 4^k` amplitude steps on `k` qubits (`gates · 2^k`
  per basis vector), and the kernel keeps every
  intermediate term until the declaration ends, so memory runs out before
  time does. Measured (gates counted over both sides): three qubits and six
  gates, 0.1 s; four qubits and 59 gates, 3 s; five qubits and 108 gates,
  10 s; seven qubits and 32 gates run past 6 GB and are killed.
- Memory is per declaration: several small lemmas composed by `trans` and
  `append` survive where one large `decide` does not. The same holds for one
  decision: `checkEquivAt a b y` is the check on the basis vector `y` alone,
  a file proves it on ranges of basis vectors, one theorem per range, and
  `equivalent_of_allBelow` assembles them (`CircuitEq/Chunk.lean`:
  `AllBelow.zero`, `AllBelow.add`). Such a file starts with
  `set_option Elab.async false`, or the memory of one declaration is not
  returned before the next starts. Seven qubits and 32 gates decide this
  way in 78 s under 2 GB.
- Do not `decide` through `denote` itself; its closures defeat the kernel's
  cache and the cost becomes exponential in depth.

Beyond what a `decide` reaches you need an argument: commute and cancel gates
with the lemmas of `Gates.lean`, cut the circuits and compose the pieces, or
build a representation that does not pay `2^n` and prove it sound.

## Tools

- The Lean language server tools (`lean-lsp`): `lean_diagnostic_messages`,
  `lean_goal`, `lean_multi_attempt`, `lean_local_search`, `lean_run_code`,
  `lean_verify`.
- `lake build Solution` builds a solution; `lake env lean Path/File.lean`
  checks one file whose imports are built. One lake process at a time, and
  not while the language server is building.
- `autoImplicit` is off. Style warnings do not matter in a solution; errors
  do.
