# Scale test: the fragment checkers on larger circuits

`scripts/scale_test.py` generates seeded random circuits of increasing
size, optimises them with PyZX 0.9.0, and asks the kernel to certify each
pair with the checker for its fragment, plus a gate-deleted mutant that the
checker must reject. Two Lean files per size, one with only the
definitions and one with the theorems, separate elaboration from kernel
time. Run on an Apple M4 with 16 GB, warm oleans, a 600 s cap per file and
a watchdog that kills any Lean process above 6 GB. Results in
`results.json`; regenerate the table with `--table`.

## Results (16 September 2026)

| Family | Qubits | Gates | T-count | Optimised gates | In fragment | Defs only | With theorems | Kernel share | Peak memory | Status |
|---|---:|---:|---:|---:|---|---:|---:|---:|---:|---|
| clifford | 20 | 200 | 0 → 0 | 597 | yes | 2.6 s | 8.9 s | 6.3 s | 3.18 GB | ok |
| clifford | 40 | 400 | 0 → 0 | 2346 | yes | 3.0 s | 65.6 s | — s | 6.15 GB | error |
| clifford | 80 | 800 | 0 → 0 | 8261 | yes | 13.3 s | 393.3 s | — s | None GB | error |
| cnot_t | 10 | 100 | 30 → 18 | 96 | yes | 16.0 s | 1.8 s | -14.2 s | 1.81 GB | ok |
| cnot_t | 20 | 200 | 71 → 39 | 183 | yes | 1.7 s | 2.1 s | — s | 1.91 GB | error |
| cnot_t | 40 | 400 | 129 → 63 | 368 | yes | 1.8 s | 3.5 s | — s | 2.25 GB | error |
| cnot_t | 80 | 800 | 271 → 155 | 783 | yes | 2.3 s | 10.6 s | — s | 3.49 GB | error |

"Status: error" rows are the watchdog or the cap (Clifford 40 and 80) or a
refused proof (CNOT+T 20, 40 and 80), see below. The CNOT+T 10-qubit row's
definitions-only time is a cold olean load, not elaboration.

## What the ladder found

**The tableau (Clifford, `≡ₛ`).** The 20-qubit pair certifies in 8.9 s,
about 6 s of it kernel time, at 3.2 GB. At 40 qubits the kernel was killed
at 6.3 GB after 65 s; at 80 qubits it was still running after 6.5 minutes
without reaching 6 GB when it was stopped by hand. Two things are going on.
PyZX's `full_reduce` plus extraction is a *re-synthesis*: on a random
Clifford circuit it returns the canonical, dense form of a generic Clifford
operator, about `1.5 n²` gates (597, 2346 and 8261 for 200, 400 and 800
input gates), so the pairs are much larger than the inputs and nothing like
the structured encoders where the same pipeline shrinks circuits. And the
kernel's `whnf` cache retains every intermediate row table for the whole
declaration, so memory, not time, is the ceiling: a few thousand gates times
a hundred rows on this machine. Chunked evaluation is the lever
(`QUEUE.md`, item 1). A fairer ladder for the tableau uses structured
Clifford families (GHZ and cat-state ladders, syndrome extraction) or
inputs sparse enough not to be generic.

**The phase polynomial (CNOT+T, `≡ᵤ`) is sound but not complete, and the
ladder found it.** The 10-qubit pair passed; the 20-, 40- and 80-qubit pairs
were *refused*: `check` returned `false`, although a phase-tracking oracle
shows the circuits agree, with identical phase, on every one of 2000 random
basis states. The reason is that the parity-basis coefficient vector the
module uses as its "normal form" is not an invariant of the unitary. Over
`ℤ/8` the parities are linearly dependent: `Z` on the parity `a ⊕ b` equals
`Z` on `a` times `Z` on `b` (coefficient 4 redistributes), on three wires
the seven parities with coefficient 2 sum to a multiple of 8, and on four
wires a `T` on each of the fifteen parities is the identity. Numerically,
for three wires the kernel of the coefficient-to-function map has 32
elements, not the 16 that the `Z` relation alone would give. PyZX's ZX
rewrites move phases along exactly these relations, so equivalent circuits
receive different coefficient vectors. The 20-qubit forms differ by a `Z`
on wire 3 and one extra term.

The invariant is the phase *function* `𝔽₂ⁿ → ℤ/8`, and its representation
as a multilinear polynomial is unique (Möbius inversion). Because `2³ ≡ 0`
modulo 8 it has degree at most 3: a parity term `k · (m · y)` expands to
`k · yᵢ` on each wire of `m`, `−2k · yᵢ yⱼ` on each pair and `4k · yᵢ yⱼ yₗ`
on each triple, using `s mod 2 ≡ s − 2·C(s,2) + 4·C(s,3) (mod 8)`. Stored
as `n` counters mod 8, a mod-4 counter per pair and a bit per triple (bit
planes as `Nat` masks), a phase gate on a parity of weight `w` costs
`O(w²)` bit operations and the form is `O(n³)` bits. That canonical form,
with the soundness proof re-done against it, is the top item of
`QUEUE.md`; until it lands, a `false` from `phasePolyChecker` means "not
decided", exactly as the `Checker` contract says, and `T·T = S`-style
merges on a single parity still pass.

A smaller usability point: when `decide +kernel` refuses a proof on a
circuit of a few hundred gates, Lean's error message fails to pretty-print
("maximum recursion depth has been reached"), hiding the reason; `#eval`
on `check` and on the two forms is the way to see it.

## Reproduce

```bash
/tmp/circuiteq-pyzx-venv/bin/python scripts/scale_test.py --family clifford --sizes 20 40 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
/tmp/circuiteq-pyzx-venv/bin/python scripts/scale_test.py --family cnot_t --sizes 10 20 40 80 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
```
