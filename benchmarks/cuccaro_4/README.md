# Cuccaro four-bit adder: bounded certificate replay

`original.qasm` and `pyzx.qasm` are byte-for-byte copies of the survey's
`cuccaro_4/original.qasm` and `cuccaro_4/pyzx_teleport.qasm`. The generator
and its arithmetic sanity checks are in `scripts/tcount_survey.py`: carry-in
on wire 0, interleaved input bits, and carry-out on wire 9. PyZX 0.9.0 uses
`teleport_reduce` followed by `basic_optimization`. The Lean translation
expands CZ as H; CX; H and uses the existing diagonal rotation convention.

`CircuitEq/Benchmarks/Cuccaro4.lean` contains the original 137 instructions,
the optimized 155 instructions, and exactly the eight windows recorded in
`benchmarks/survey/results.json`. T-count changes from 56 to 48. The tactic
finds 196 certificate steps. No alignment or circuit was changed to make
the memory test pass.

## Measurement, 22 September 2026

Apple M4, the pinned Lean v4.30.0-rc2, warm imports, one Lean process at a
time, `set_option Elab.async false`. RSS includes imported modules. GB
means decimal bytes; GiB means bytes divided by `2^30`.

| Replay | Wall time | Peak RSS | Result |
|---|---:|---:|---|
| Prior survey, one declaration | 12.2 s until killed | 4.6 GB | watchdog kill, historical survey record |
| Eight-step chunks, separately checked windows | 10.9 s | 1.99 GB (1.85 GiB) | proves below 2 GB |

The final run reported 1,991,081,984 bytes peak RSS.

Chunking replay alone was insufficient: a five-wire window still kept all
of its basis evaluations in one kernel reduction cache. The tactic now
proves windows before replay: phase-polynomial checks remain symbolic;
other windows use `AllBelow` with one basis vector per declaration. A
`Checker.ofProof` accepts only the exact window pair already proved. Each
replay segment still checks the placement, cache index and every move;
semantic equivalences compose with `Equivalent.trans`. Endpoints at chunk
boundaries are literal circuits, so later segments cannot unfold the
preceding replay. All leaf checks use `decide +kernel`.

## Reproduce

After `lake build`, with no language server or other Lake process running:

```bash
/usr/bin/time -l lake env lean CircuitEq/Benchmarks/Cuccaro4.lean
python scripts/check_pyzx_benchmarks.py cuccaro_4  # pyzx==0.9.0
```

The checker reproduces the optimizer output and compares both Lean lists
against the QASM. `lake build` includes the benchmark, and CI's axiom check
and `leanchecker` replay include its auxiliary proofs. The synthetic
move-only ladder is recorded in `benchmarks/scale/README.md`.

This change bounds retained replay work, not search difficulty or total
proof size. Checkpoint storage still grows with circuit size times chunk
count; replay still traverses prefixes, and wide basis windows still cost
exponentially in their width. Phase goals and direct `circuit_replay`
macros retain their original single-declaration behavior.
