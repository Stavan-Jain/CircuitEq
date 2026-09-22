# PLAYBOOK — deciding a circuit pair with CircuitEq

The prover's guide to this library: what exists, what it costs, and in which
order to try it on a concrete pair. `CLAUDE.md` is for people who extend the
library; this file is for whoever has two circuits and wants a proof. The
agent harness (`scripts/agent_harness.py`) installs it as the `CLAUDE.md` of
every `full` run, so it is the agent's only description of the library. It is
versioned with the library: when a checker, a tactic, a certificate step or
a block theorem lands, update the decision list below in the same commit.

Last brought in line with the library at `83cc1d7` (22 September 2026:
composition up to a global phase, `≡ₚ[k]`, certificates and windows up to
phase, the phase gadget; on top of chunked kernel evaluation, the sparse
phase-polynomial fold and the kernel replay in the trust policy).

## The objects

- A circuit on `n` qubits is `Quantum.Circuit n`, a list of instructions in
  time order: `[g₁, g₂]` applies `g₁` first. Gates are `H X Y Z S Sdg T Tdg`
  on a wire and `CX c t`; wires are `Fin n` literals.
- Write Lean inside `namespace Quantum.Circuit.<Name>` with `open Instr`, as
  `Solution.lean` and the modules under `CircuitEq/Benchmarks/` do. Then
  `Circuit 5`, `[H 0, CX 0 1, T 1]` and the notation below resolve. Ascribe
  one side of a literal equivalence, `([H 0, H 0] : Circuit 1) ≡ᵤ []`: the
  qubit count is not inferable from the list.
- Four relations, in `CircuitEq/Semantics.lean`:
  - `a ≡ᵤ b` (`Equivalent`): `∀ ψ, denote a ψ = denote b ψ`. It has
    `refl`, `symm`, `trans`, `append`, `cons`, and `calc` works.
  - `a ≡ₚ b` (`EquivalentUpToPhase`): equal up to a power of `ω = e^{iπ/4}`.
    It has everything `≡ᵤ` has: `refl`, `symm`, `trans`, `append`, `cons`
    (and `in_context` in `Rewriting.lean`, `rename` in `Embedding.lean`),
    and `calc` mixes `≡ᵤ` and `≡ₚ` steps in any order. `h.toUpToPhase`
    weakens `≡ᵤ` to it.
  - `a ≡ₚ[k] b` (`EquivalentWithPhase`, `k : Fin 8`): the same with the
    phase named, `a = ω^k · b`; `≡ₚ` is `∃ k` of it. Named phases add
    (`h₁.append h₂ : … ≡ₚ[j + k] …`), `h.cast (by decide)` restates an
    exponent, and `≡ₚ[0]` is `≡ᵤ` (`equivalentWithPhase_zero_iff`). Keep the
    space in `a ≡ₚ [X 0]`: `≡ₚ[` is its own token.
  - `a ≡ₛ b` (`EquivalentUpToScalar`): equal up to a nonzero scalar; what
    the Clifford tableau certifies. It has `refl`, `symm`, `trans`,
    `append`; `h.toUpToScalar` weakens `≡ᵤ` and `≡ₚ` to it.
- `denote` is the trusted definition. Do not unfold it to evaluate a
  circuit; the evaluators below are proved equal to it and are what runs.

## What counts as a proof

A proof here is checked by the Lean kernel and depends on the axioms
`propext`, `Classical.choice` and `Quot.sound` only. Both halves are checked
by the repository's CI, and you can check both yourself.

- **The axioms.** `#print axioms name`, or the language server's
  `lean_verify`. This rules out `sorry`, `native_decide` and any new `axiom`.
- **The kernel replay.** Never set a `debug.*` option.
  `set_option debug.skipKernelTC true` makes Lean add a declaration without
  sending it to the kernel, and `decide +kernel`, the leaf of every proof
  here, leaves its whole check to the kernel: under the option a false leaf
  compiles without an error and its axiom report is clean. So every built
  module is also replayed through the kernel, in a process where none of the
  module's options or meta code runs, and that replay rejects it. On your
  own module:

  ```bash
  LEAN_NUM_THREADS=1 lake env leanchecker -v Solution
  ```

  It repeats every kernel check of the module, so it costs the module's
  kernel time again (15 s for a small one, mostly loading imports). Three
  rules. Always one thread: each extra thread loads its own copy of the
  mathlib imports, about 2 GB, and the default thread count was killed at
  26 GB on a 16 GB machine. Always through `lake env` from the project
  directory: run bare, the binary makes elan download another toolchain. And
  it is a lake process, so not beside another one. It reads the `.olean`
  files under `.lake/build`, so build first.
  `scripts/check_debug_options.py` is the text guard CI runs for the obvious
  spellings; it is an early warning, the replay is the defence.

## The cost model

Every leaf of a proof here is a kernel evaluation of a `Bool`: a checker's
`check`, or the `Decidable` instance of `≡ᵤ` or `≡ₚ`, closed by
`decide +kernel`. Bare `decide` stalls on the first rational addition.
`native_decide` is banned.

- **The basis evaluator** (what `by decide +kernel` runs on a goal `a ≡ᵤ b`,
  `a ≡ₚ b`, or a negation) evaluates both circuits on all `2^k` basis
  vectors of `k` qubits, `gates · 4^k` amplitude steps in all, and the
  kernel keeps every intermediate term until the declaration ends, so
  memory runs out before time does. In one declaration, measured (gates
  counted over both sides): three qubits and six gates, 0.1 s; four qubits
  and 59 gates, 3 s; five qubits and 108 gates, 10 s; seven qubits and 32
  gates run past 6 GB and are killed.
- **Memory is per declaration, so heavy checks are chunked**
  (`CircuitEq/Chunk.lean`): one theorem per range of basis vectors or of
  tableau generators, each its own `decide +kernel`, assembled by a term of
  constant size. Peak memory is one chunk's and the time is unchanged. The
  seven-qubit pair above decides on its full basis in 78 s under 2 GB, at
  0.6 s and 165 MB per basis vector; expect five minutes at eight qubits
  and over an hour at ten.
- **Any file with more than a few kernel-heavy declarations starts with
  `set_option Elab.async false`**, whatever the declarations are: chunks of a
  basis decide, tableau ranges, or one `circuit_windows` lemma per segment of
  a long pair. Without it the memory of one declaration is not returned
  before the next starts, and the file's peak is the sum, not the maximum
  (sixteen declarations peaked at 3.6 GB with asynchronous elaboration
  on, 2.6 GB with it off). Splitting
  into several modules bounds it further.
- **Loading the imports costs 1.7 s and 1.8 GB** before any proof runs, so
  that much of a memory limit is already spent.
- **The symbolic checkers never build anything of size `2^n`.** The phase
  polynomial is linear in the gate count: 800 random gates on 80 wires in
  1.9 s at 2.5 GB, a CCZ network of 10200 gates on 300 wires in 10 s at
  5.3 GB (what grows is a `C(n,3)`-bit plane, so width costs memory). The
  tableau walks the circuit once per generator, `2n · gates`
  steps at 0.2 to 0.3 ms: 15 qubits in 0.3 s and 600 gates on 20 qubits in
  6 s in one declaration, which runs out of memory near 40 qubits and 2000
  gates. In chunks: 40 qubits and 2346 gates in 39 s, 80 qubits and 8261
  gates in 7 minutes at 4 GB, structured circuits on 200 qubits in seconds.
- **Certificates.** `circuit_simp` and `circuit_windows` search in meta code
  and hand the kernel one list of steps to replay; the cost is linear in the
  steps, plus each window on its own wires. A 155-gate certificate has been
  seen to run past 4 GB, so long alignments are split too. Replayed up to a
  phase, the same certificate costs about 1.2 times the exact one (`tof_3`:
  0.19 s against 0.16 s).

## Decision list for a concrete pair

Look at the two gate sets first, then take the first entry that applies.

1. **At most five qubits.** `by decide +kernel` proves `a ≡ᵤ b`, `a ≡ₚ b`,
   `a ≡ₚ[k] b`, `¬ (a ≡ᵤ b)` or `¬ (a ≡ₚ b)` outright. (`≡ₛ` has no
   `Decidable` instance.)
   **Six to about eight qubits: the same decision in chunks.** One theorem
   per range of basis vectors and `equivalent_of_allBelow` to assemble them;
   the cost is the brute-force `gates · 4^n`, so check the budget first.

   ```lean
   set_option Elab.async false   -- first line after the imports

   theorem r0 : (List.range' 0 16).all (checkEquivAt original optimized) = true := by
     decide +kernel
   theorem r1 : (List.range' 16 16).all (checkEquivAt original optimized) = true := by
     decide +kernel
   -- … one per range, up to 2 ^ n
   theorem equiv : original ≡ᵤ optimized :=
     equivalent_of_allBelow (((AllBelow.zero _).add r0).add r1)
   ```

   `scripts/chunks.py` writes the theorems and the assembling term (see
   "Tools"). Up to a phase: `checkEquivUpToPhaseAt a b k` with
   `equivalentWithPhase_of_allBelow : … → a ≡ₚ[k] b`, or
   `equivalentUpToPhase_of_allBelow (by decide)` for `≡ₚ`, where the file
   names the phase `ω ^ k`, `k < 8`; find `k` on one basis vector first.
2. **Only `CX` and `Z S Sdg T Tdg` on both sides.**
   `(phasePolyChecker n).sound _ _ (by decide +kernel) : a ≡ᵤ b`
   (`CircuitEq/PhasePoly.lean`). The form is canonical, so on this fragment
   a failed check means the pair is inequivalent, and
   `phasePolyRefutes_sound (by decide +kernel) : ¬ a ≡ᵤ b` proves that. `H`,
   `X` and `Y` end the fragment.
3. **Only Clifford gates, `H X Y Z S Sdg CX`.**
   `(tableauChecker n).sound _ _ (by decide +kernel) : a ≡ₛ b`
   (`CircuitEq/Tableau.lean`). It certifies `≡ₛ` and nothing stronger. Past
   a few thousand gates, or about 30 qubits, chunk it: `tableauCheckGen a b
   g` checks generator `g` of the `2n`, and `tableau_sound_of_allBelow`
   turns `AllBelow (tableauCheckGen a b) (2 * n)` into `a ≡ₛ b`, with the
   ranges proved as in entry 1 (four to sixteen generators per theorem).
   The tableau is sound and not proved complete: `tableauCheck a b = false`
   or a failing generator is not a refutation, though `witness a b`
   names the first Pauli generator whose images differ, which tells you
   where to look. For exact `≡ᵤ` of a Clifford pair use the entries below.
4. **The same gates reordered, or pairs that cancel.** `by circuit_simp`. It
   cancels adjacent-after-commuting inverse pairs and then pulls each gate
   of `b` to the front of what is left of `a`, checking every move.
5. **Local rewrites on a kept skeleton** (phase folding, phase
   teleportation, peephole passes). `by circuit_windows [(a₁, b₁), …]`
   (`CircuitEq/Tactic.lean`). A window is a before and after pair of gate
   lists on the full register that touch few wires; list the windows in the
   order they fire as `b` is read from the left. The tactic decides each
   window on its own wires (the phase polynomial when it applies, else the
   basis at cost `2^k`) and checks every other move as a commutation. It
   does not search for the alignment: a move it cannot license fails naming
   the gate, a false window is reported as false. A window with an empty
   side is an insertion or a deletion; a window with the same gates on both
   sides is a commutation the syntactic check does not know.
   - What commutes (`Instr.CanCommute`, `CircuitEq/Rewriting.lean`): equal
     gates; disjoint wires; two diagonal gates on one wire; a diagonal gate
     on a CNOT's control; `X` on a CNOT's target; CNOTs whose controls avoid
     each other's targets. What cancels (`Instr.CanCancel`): inverse pairs.
   - Finding the windows: put both lists in a canonical order under those
     commutations, diff them, and merge or widen a window the tactic
     refuses. `scripts/tcount_survey.py` does this (see "Tools").
   - A long pair is cut into segments first, one lemma per segment,
     assembled by `Equivalent.append` or a `calc`. The alignment search is
     quadratic or worse and does not finish on a thousand gates taken whole;
     on segments of fifty gates it takes under a second each. Cut where the
     two circuits agree on the state so far (compare the prefixes
     numerically on one random state). Keep a segment under about eighty
     gates: a 155-gate certificate has run past 4 GB.
   - Price every window before building: a window on `k` wires is a basis
     decide of `gates · 4^k` steps in one declaration. Three wires are
     cheap, five are seconds, six with thirty gates is already past 4 GB,
     and eight is out of reach; a window that wide means the cut or the
     alignment is wrong, so refine it, do not build it. Build the narrow
     segments first, with `sorry` on the wide ones, to learn that the rest
     checks.
6. **Block structure**: a Hadamard layer moved through a CNOT network, an
   encoder re-synthesised with reversed CNOTs. Name the blocks
   (`layer g wires`, `hLayer n`, `cnotNetwork edges`, `hOn s`), equate the
   circuit to the block form by `rfl`, apply the block theorem, close the
   rest with `circuit_simp`:

   ```lean
   theorem t : c₁ ≡ᵤ c₂ :=
     calc c₁ = layer .H seed ++ cnotNetwork edges ++ hLayer n := rfl
       _ ≡ᵤ _ := layer_cnotNetwork_hLayer seed (by decide) edges (by decide)
       _ ≡ᵤ c₂ := by circuit_simp
   ```

   `layer_cnotNetwork_hLayer` turns `layer .H seed ++ cnotNetwork edges ++
   hLayer n` into `layer .H ((List.finRange n).diff seed) ++ cnotNetwork
   (swapEndpoints edges)`, for every `n`. Also in `CircuitEq/Layers.lean`
   and `CircuitEq/Structural.lean`: `hLayer_hLayer`, `hOn_symmDiff`,
   `cnotNetwork_perm`, `cnotNetwork_layer`, `layer_layer_cancel`; in
   `CircuitEq/Rewriting.lean`: `cnot_hadamards_reverse`, `layer_perm`,
   `perm_equivalent` (every pair in the block must commute), `blocks_comm`.
7. **Composition**, when no single entry covers the pair.
   - `calc` and `Equivalent.trans`; `h₁.append h₂`; `h.in_context pre post`
     rewrites a window inside a fixed prefix and suffix.
   - `h.rename f` and `Equivalent.of_rename f h rfl rfl` place an identity
     decided on `k` qubits on `k` wires of any register; `wires₁ i`,
     `wires₂ hij` and `wires₃ …` build the embedding
     (`CircuitEq/Embedding.lean`). This is how a window costs `2^k` and not
     `2^n`. The same names exist for `≡ₚ` and `≡ₚ[k]`
     (`EquivalentWithPhase.rename`, `.of_rename`, `.in_context`).
   - Cut both circuits at a common layer and prove the halves separately,
     each by its own entry of this list, each in its own lemma.
   - Create a window by inserting a cancelling pair:
     `cancel_of_mul_eq_one`, `Instr.CanCancel.sound`, `fuse`, `fuse₃`.
   - `inverse c` with `denote_inverse_denote` for an argument about a
     residual (one prefix times the inverse of the other).
8. **A pair equal only up to a global phase.** PyZX and TZAP drop
   scalars, so if `a ≡ᵤ b` is refuted, try `a ≡ₚ b` before suspecting the
   alignment. State the goal on `≡ₚ` and use exactly the tools you would for
   `≡ᵤ`: `circuit_windows [(a₁, b₁), …]` accepts `≡ₚ` and `≡ₚ[k]` goals
   unchanged, and `circuit_simp`, whose moves are all exact, accepts `≡ₚ`
   and `≡ₚ[0]`. Each window may then hold only up to a phase of its own
   (`Z X` against `X Z` is `ω⁴`), found on its own wires at cost `2^k`, and
   every other move stays exact.
   - To name the phase, state `a ≡ₚ[k] b`. If `k` is wrong the error names
     the right one, so guessing `0` is a fine way to find it.
   - Prove a long circuit segment by segment, one declaration each, and
     compose with `append`. The exponents add: `seg₁.append seg₂ : … ≡ₚ[j +
     k] …` closes a goal stated with the numeral, and `.cast (by decide)`
     restates an exponent.
   - For an exact statement,
     `(equivalentWithPhase_iff_phaseGadget k i _ _).1 h : a ≡ᵤ b ++ phaseGadget k i`.
     The gadget is Clifford-only (T-count 0, `(SH)³ = ω·I`) and commutes
     with everything (`phaseGadget_comm`), so a phase-only pair becomes an
     exact one at no `T`-cost.
   - A certificate found by `set_option trace.circuit.certificate true`
     replays up to phase with `circuit_replay_phase defaultPhaseFinders
     steps` (`replayPhase_sound`, `replayUpToPhase_sound`).
   - Never decide a phase on the whole register when a window can carry it.
     The Clifford tableau names no phase, so it cannot justify a phase
     window yet.
9. **Refuting.** Up to five qubits: `by decide +kernel` on the negation. In
   the `CX` plus diagonal fragment: `phasePolyRefutes_sound`. Beyond those
   there is no ready-made refuter, but one basis vector on which the two
   evaluations differ is enough, and it costs `gates · 2^n`, not
   `gates · 4^n` (0.6 s at seven qubits). The library does not have the
   lemma yet; this proof of it is checked:

   ```lean
   theorem not_equivalent_of_checkEquivAt {n : ℕ} {a b : Circuit n} {y : ℕ}
       (hy : y < 2 ^ n) (h : checkEquivAt a b y = false) : ¬ a ≡ᵤ b := by
     intro he
     have hall := (checkEquiv_iff a b).2 he
     rw [checkEquiv_eq_all, List.all_eq_true] at hall
     have hy' := hall y (List.mem_range.2 hy)
     rw [h] at hy'
     exact Bool.false_ne_true hy'

   theorem differ : checkEquivAt original optimized 0 = false := by decide +kernel
   theorem not_equiv : ¬ (original ≡ᵤ optimized) :=
     not_equivalent_of_checkEquivAt (by decide) differ
   ```

   Find the basis vector in a scratch file with
   `#eval (List.range (2 ^ n)).map (checkEquivAt original optimized)`, or
   numerically outside Lean. There is no such route for `≡ₛ`: a tableau
   generator that fails is not a refutation.

Before investing in either theorem, find out which one is true: a numerical
comparison of the two unitaries outside Lean is an untrusted oracle, and a
cheap one.

## Tools

- The Lean language server tools (`lean-lsp`): `lean_diagnostic_messages`
  to localise errors, `lean_goal` for the proof state, `lean_multi_attempt`
  to try several tactics at once, `lean_local_search` before guessing a
  lemma name, `lean_run_code` for a self-contained probe, `lean_verify` for
  the axioms of one theorem.
- `lake build Solution` builds a solution; `lake env lean Path/File.lean`
  checks one file whose imports are built. One lake process at a time, and
  not while the language server is building.
- `LEAN_NUM_THREADS=1 lake env leanchecker -v Module` replays a built module
  through the kernel ("What counts as a proof"). Never without the thread
  cap, never without `lake env`.
- `set_option trace.circuit.certificate true in` before a theorem prints
  the certificate a tactic found, in the syntax `circuit_replay` accepts.
- `scripts/certificate.py` is a pure-Python mirror of the certificate
  language (`align`, `replay`, `fmt_certificate`, and
  `replay_phase(default_phase_finders(…), steps, c)`, which returns the
  phase with the result), for searching outside Lean. Its command line
  covers only the repository's own benchmarks; import it for your pair.
- `scripts/chunks.py` (no dependencies) writes a chunked check:

  ```python
  import sys; sys.path.insert(0, "scripts")
  from chunks import CHUNK_HEADER, chunk_theorems
  lines, term = chunk_theorems("checkEquivAt original optimized", 2 ** 7, 16, "r")
  print(CHUNK_HEADER, *lines, sep="\n")
  print(f"theorem equiv : original ≡ᵤ optimized :=\n  equivalent_of_allBelow ({term})")
  ```

  The same call with `"tableauCheckGen original optimized"`, `2 * n` and
  `tableau_sound_of_allBelow` chunks a tableau.
  `scripts/chunked_decide.py` and `scripts/scale_test.py --chunk` are the
  emitters for the repository's own benchmark modules and scale ladder.
- `scripts/tcount_survey.py` holds the alignment search and a numpy
  comparison of unitaries. It imports `numpy` and `pyzx`; if they are
  missing, diff the lists yourself with `difflib`.

  ```python
  import sys; sys.path.insert(0, "scripts")
  import tcount_survey as ts
  xs = ts.parse(["H 0", "CX 0 1", "T 1"])      # gate strings as in the Lean lists
  ys = ts.parse(["CX 0 1", "H 0", "T 1"])
  print(ts.compare(ts.unitary(xs, 2), ts.unitary(ys, 2)))   # untrusted oracle
  al, attempts, which = ts.best_alignment(xs, ys)
  print(ts.lean_windows(al) if al else attempts)            # windows for `circuit_windows`
  ```

## Module map

`CircuitEq/` holds, in dependency order: `Zeta8` (the coefficient field
`ℚ(ζ₈)`), `Bits`, `Gates` (`Gate1`, the matrices, `applyOne`, `applyCNOT`),
`Dyadic` (the ring the evaluator computes in), `Chunk` (`AllBelow`, a check
proved one index range per declaration), `Semantics` (`Instr`, `Circuit`,
`denote`, the relations `≡ᵤ`, `≡ₚ`, `≡ₚ[k]`, `≡ₛ` and their algebra,
decidability, `checkEquivAt`, `findPhase`), `Checker` (the `check` + `sound`
contract, `PhaseFinder`), `Structural` (fusion, commutation, layers,
`phaseGadget`), `Support` (wire sets as bitmasks), `PhasePoly`, `Tableau`,
`Rewriting`, `Layers`, `Embedding` (`rename`, the locality theorem),
`Certificate` (`Step`, `replay`, `replay_sound`, `circuit_replay`;
`replayPhase_sound`, `circuit_replay_phase`), `Tactic`, `Examples` (worked
identities, the quickest way to see each tool
used), and `Benchmarks/` (whole pairs proved with the patterns above).

## Conventions that bite

- `decide +kernel`, never bare `decide`, for anything about circuits.
- A file with more than a few kernel-heavy declarations starts with
  `set_option Elab.async false` (the cost model says why).
- No `debug.*` option, ever.
- `autoImplicit` is off: bind every variable.
- The tactics read lists by `whnf`, so named `def`s, `layer`, `cnotNetwork`
  and `hLayer` are fine as their inputs; a list built by a recursive
  function may need `show` or `rfl` to the literal first.
- Style warnings do not matter in a solution; errors do.
