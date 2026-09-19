# Scale test: the fragment checkers on larger circuits

`scripts/scale_test.py` generates seeded random circuits of increasing
size, optimises them with PyZX 0.9.0, and asks the kernel to certify each
pair with the checker for its fragment, plus a gate-deleted mutant that the
checker must reject (for the phase polynomial: refute, by the completeness
theorem). Two Lean files per size, one with only the definitions and one
with the theorems, separate elaboration from kernel time. Run on an Apple
M4 with 16 GB, warm oleans, a 600 s cap per file and a watchdog that kills
any Lean process above 6 GB. Results in `results.json`; regenerate the
table with `--table`.

## Results (16 September 2026)

| Family | Qubits | Gates | T-count | Optimised gates | In fragment | Defs only | With theorems | Kernel share | Peak memory | Status |
|---|---:|---:|---:|---:|---|---:|---:|---:|---:|---|
| clifford | 20 | 200 | 0 → 0 | 597 | yes | 2.6 s | 8.9 s | 6.3 s | 3.18 GB | ok |
| clifford | 40 | 400 | 0 → 0 | 2346 | yes | 3.0 s | 65.6 s | — s | 6.15 GB | error |
| clifford | 80 | 800 | 0 → 0 | 8261 | yes | 13.3 s | 393.3 s | — s | None GB | error |
| cnot_t | 10 | 100 | 30 → 18 | 96 | yes | 1.7 s | 1.8 s | 0.1 s | 1.83 GB | ok |
| cnot_t | 20 | 200 | 71 → 39 | 183 | yes | 1.8 s | 2.0 s | 0.2 s | 1.89 GB | ok |
| cnot_t | 40 | 400 | 129 → 63 | 368 | yes | 1.9 s | 2.8 s | 0.9 s | 2.07 GB | ok |
| cnot_t | 80 | 800 | 271 → 155 | 783 | yes | 2.3 s | 6.2 s | 3.9 s | 2.85 GB | ok |

The Clifford rows are the first run of the ladder (the tableau checker is
unchanged since); the CNOT+T rows are the rerun on the canonical phase
polynomial, and each "ok" is two theorems, `original ≡ᵤ optimized` and
`¬ (original ≡ᵤ mutant)`. "Status: error" is the watchdog or the cap. The
definitions-only column is dominated by loading the imports, about 1.7 s
and 1.7 GB.

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
a hundred rows on this machine. Chunked evaluation, one theorem per
generator, is the lever (`QUEUE.md`, item 3). A fairer ladder for the
tableau uses structured Clifford families (GHZ and cat-state ladders,
syndrome extraction) or inputs sparse enough not to be generic.

**The phase polynomial (CNOT+T, `≡ᵤ`): the first run found it incomplete,
the rerun certifies every rung.** In the first run the 10-qubit pair passed
and the 20-, 40- and 80-qubit pairs were *refused*: `check` returned
`false` although a phase-tracking oracle showed the circuits agree on every
one of 2000 random basis states. The parity-basis coefficient vector the
module then used as its "normal form" is not an invariant of the unitary:
over `ℤ/8` the parity functions are linearly dependent (`Z` on `a ⊕ b`
equals `Z a · Z b`, on three wires the seven parities with coefficient 2
sum to a multiple of 8, on four wires a `T` on each of the fifteen parities
is the identity; for three wires the kernel of the coefficient-to-function
map has 32 elements, not 16), and PyZX's rewrites move phases along exactly
these relations. Nothing unsound happened: the `Checker` contract reads
`false` as "not decided". But the 10-qubit pass was luck.

The fix is the canonical form in `CircuitEq/PhasePoly.lean` now: the phase
function as its multilinear polynomial over `ℤ/8`, unique by Möbius
inversion and of degree at most three because `2³ ≡ 0`, stored as `Nat`
bit planes in the combinatorial number system (`C(n,2)` and `C(n,3)` bits
for the pairs and triples), updated by a ripple-carry adder on planes and
one shift-and-or per set bit of the parity. Its soundness proof was redone
and a completeness theorem added (`PhasePoly.complete`: equal unitaries
give equal forms), so the exported `phasePolyRefutes` turns a `false` into
a proof of `¬ a ≡ᵤ b`; the mutant rows above are those theorems. The
three relations are now tests in the module (`Z_parity`, `seven_S`,
`fifteen_T`).

Profiling the rerun changed the representation twice more, and the numbers
are worth keeping. With the rows as a `List ℕ`, each CNOT's `List.set` and
`List.getD` walks left about 1.5 MB of retained terms in the kernel's
cache (structural recursion through `brecOn`), which was half the cost of
the 80-qubit rung; packing the rows into one `Nat`, so a CNOT is a shift
and an xor, removed it. Indexing the triple plane with stride `n²` made it
`n³` bits, which mattered less than expected (5.2 GB to 4.5 GB at 80
qubits); the combinatorial indexing keeps it at `C(n,3)`. Peeling set bits
with `Nat.log2` was slower than testing each index, because the kernel does
not accelerate `log2`. What remains is the phase gates on dense parities:
about 10 ms and 2.5 MB per gate at 80 wires, 271 of them in the 80-qubit
original, which is the 3.9 s and the 1.1 GB above the import baseline.

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
