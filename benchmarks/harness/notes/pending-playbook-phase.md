# Pending playbook text: pairs equal only up to a global phase

Not in `PLAYBOOK.md` yet, on purpose. The playbook is installed as the only
guide of an agent under test, so it may describe only what the library
commit under test contains. The tools below exist in the uncommitted branch
`claude/phase-composition` (worktree
`.claude/worktrees/agent-a4015d651918f20ea`, based on origin/main `a9a80ed`;
builds warning-free, axiom policy and one-thread kernel replay pass, checked
19 September 2026). When that branch lands:

1. replace the `≡ₚ` bullet of "The objects" (it says `≡ₚ` has no
   composition lemmas) and add the entry below to the decision list;
2. add `≡ₚ[k]`, `phaseGadget`, `replayPhase_sound` and
   `circuit_replay_phase` to the module map and the tools;
3. name the new commit at the top of the playbook;
4. harness tasks with `"relation": "p"` then become provable piece by piece:
   TZAP's and PyZX's outputs on the 1000-gate circuit are all phase-only
   (`benchmarks/harness/notes/README.md`).

## The entry

**A pair equal only up to a global phase.** PyZX and TZAP drop scalars, so
if `a ≡ᵤ b` is refuted, try `a ≡ₚ b` before suspecting the alignment. State
the goal on `≡ₚ` and use exactly the tools you would for `≡ᵤ`.
`circuit_windows [(a₁, b₁), …]` works unchanged: each window may now hold
only up to a phase of its own (`Z X` against `X Z` is `ω⁴`), found on its
own wires at cost `2^k`, and every other move stays exact. `calc` may mix
`≡ᵤ` and `≡ₚ` steps in any order. For segments use `h₁.append h₂` and
`h.in_context pre post`; to place a small fact use `h.rename (wires₂ hij)`.

To name the phase, state `a ≡ₚ[k] b` with `k : Fin 8`, meaning
`a = ω^k · b`. If `k` is wrong the error names the right one, so guessing
`0` is a fine way to find it. Named phases add: `seg₁.append seg₂ : … ≡ₚ[j + k]
…` closes a goal stated with the numeral, and `.cast (by decide)` restates
an exponent. Prove a long circuit segment by segment, one declaration each,
and compose with `append`.

For an exact statement,
`(equivalentWithPhase_iff_phaseGadget k i _ _).1 h : a ≡ᵤ b ++ phaseGadget k i`,
where the gadget is Clifford-only (T-count 0, `(SH)³ = ω·I`) and commutes
with everything (`phaseGadget_comm`). A window is decided by
`decide +kernel` on `≡ₚ[k]`, or in chunks by
`equivalentWithPhase_of_allBelow`. Keep the space in `a ≡ₚ [X 0]`: `≡ₚ[` is
its own token. Never decide a phase on the whole register when a window can
carry it.

## Caveats the subagent found

- A circuit with a degenerate `CX c c` can denote zero, so a named phase is
  not unique without the distinct-wires proviso (`[CX 0 0, Z 0, H 0, CX 0 0]`
  is `≡ₚ[1]` to itself).
- The Clifford tableau names no phase, so it cannot justify a phase window
  until `≡ₛ → ≡ₚ` is proved for Clifford circuits; the scalar replay for
  tableau windows is still open (`QUEUE.md`).
