# Scale test: the fragment checkers on larger circuits

`scripts/scale_test.py` generates seeded circuits of increasing size,
optimises them with PyZX 0.9.0, and asks the kernel to certify each pair
with the checker for its fragment, plus a gate-deleted mutant that the
checker must reject (for the phase polynomial: refute, by the completeness
theorem). Two Lean files per size, one with only the definitions and one
with the theorems, separate elaboration from kernel time. Run on an Apple
M4 with 16 GB, warm oleans, a time cap per file. Results in `results.json`;
regenerate the table with `--table`.

Families: `clifford` and `cnot_t` are random; `ghz` (the GHZ ladder),
`surface ×r` (`r` rounds of syndrome extraction of the rotated surface code,
unitary part only, on `2d² − 1` qubits) and `ccz_net` (CCZ gadgets, not yet
run) are structured. Pipelines: `full_reduce` re-synthesises, `teleport`
folds phases and keeps the skeleton, `basic` is PyZX's peephole pass alone.
"Chunk" is the number of tableau generators per declaration
(`CircuitEq/Chunk.lean`); "—" is the whole check in one declaration.

## Results (16 and 18 September 2026)

| Family | Pipeline | Qubits | Gates | T-count | Optimised gates | Chunk | Defs only | With theorems | Kernel share | Peak memory | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| clifford | full_reduce | 20 | 200 | 0 → 0 | 597 | — | 2.6 s | 8.9 s | 6.3 s | 3.18 GB | ok |
| clifford | full_reduce | 40 | 400 | 0 → 0 | 2346 | — | 3.0 s | 65.6 s | — s | 6.15 GB | error |
| clifford | full_reduce | 80 | 800 | 0 → 0 | 8261 | — | 13.3 s | 393.3 s | — s | None GB | error |
| clifford | full_reduce | 20 | 200 | 0 → 0 | 597 | 8 | 2.1 s | 6.7 s | 4.6 s | 2.07 GB | ok |
| clifford | full_reduce | 40 | 400 | 0 → 0 | 2346 | 8 | 3.1 s | 42.1 s | 39.0 s | 2.87 GB | ok |
| clifford | full_reduce | 80 | 800 | 0 → 0 | 8261 | 4 | 7.7 s | 429.6 s | 421.9 s | 3.95 GB | ok |
| ghz | full_reduce | 50 | 50 | 0 → 0 | 50 | 16 | 1.7 s | 2.3 s | 0.6 s | 1.8 GB | ok |
| ghz | full_reduce | 100 | 100 | 0 → 0 | 100 | 16 | 1.9 s | 4.0 s | 2.1 s | 1.83 GB | ok |
| ghz | full_reduce | 200 | 200 | 0 → 0 | 200 | 16 | 2.0 s | 13.5 s | 11.5 s | 1.92 GB | ok |
| surface ×2 | basic | 17 | 64 | 0 → 0 | 56 | 8 | 2.0 s | 3.0 s | 1.0 s | 1.81 GB | ok |
| surface ×2 | basic | 49 | 208 | 0 → 0 | 184 | 8 | 2.0 s | 7.9 s | 5.9 s | 1.92 GB | ok |
| surface ×2 | basic | 97 | 432 | 0 → 0 | 384 | 8 | 2.1 s | 26.6 s | 24.5 s | 2.05 GB | ok |
| surface ×1 | full_reduce | 49 | 104 | 0 → 0 | 122 | 8 | 1.8 s | 4.5 s | 2.7 s | 1.85 GB | ok |
| surface ×1 | full_reduce | 97 | 216 | 0 → 0 | 250 | 8 | 1.9 s | 14.4 s | 12.5 s | 1.93 GB | ok |
| surface ×1 | full_reduce | 161 | 368 | 0 → 0 | 436 | 8 | 2.1 s | 40.6 s | 38.5 s | 2.09 GB | ok |
| surface ×2 | full_reduce | 97 | 432 | 0 → 0 | 0 | 8 | 2.0 s | 13.8 s | 11.8 s | 1.93 GB | ok |
| cnot_t | teleport | 10 | 100 | 30 → 18 | 96 | — | 1.7 s | 1.8 s | 0.1 s | 1.83 GB | ok |
| cnot_t | teleport | 20 | 200 | 71 → 39 | 183 | — | 1.8 s | 2.0 s | 0.2 s | 1.89 GB | ok |
| cnot_t | teleport | 40 | 400 | 129 → 63 | 368 | — | 1.9 s | 2.8 s | 0.9 s | 2.07 GB | ok |
| cnot_t | teleport | 80 | 800 | 271 → 155 | 783 | — | 2.3 s | 6.2 s | 3.9 s | 2.85 GB | ok |

Every "ok" is two theorems: the equivalence (`≡ₛ` for the tableau, `≡ᵤ` for
the phase polynomial) and the mutant (`tableauCheckGen … = false` on the
generator a Python mirror of the update rules names, or
`¬ (original ≡ᵤ mutant)`). The unchunked Clifford rows are the first run of
the ladder, kept as the record of the ceiling: "error" is the 6 GB watchdog
at 40 qubits and a stop by hand at 80. The definitions-only column is
dominated by loading the imports, about 1.7 s and 1.8 GB.

## What the ladder found

**Chunked evaluation removes the memory ceiling, and the ceiling was never
time.** The kernel keeps its reduction cache for the whole of one
declaration, so the unchunked tableau died at 6.2 GB on 40 qubits and the
seven-qubit basis decide at 6.9 GB. One theorem per range of generators
(`tableauCheckGen`, `tableau_sound_of_allBelow`) certifies the same 40-qubit
pair in 39 s at 2.9 GB and the 80-qubit pair, 800 gates re-synthesised into
8261, in 7 minutes at 4.0 GB with four generators per declaration. One
theorem per basis vector (`checkEquivAt`, `equivalent_of_allBelow`,
`scripts/chunked_decide.py SteanePlus --chunk 1`) decides the seven-qubit
Steane pair, 128 basis vectors, in 78 s at 1.98 GB, which is 0.06 GB above
the imports. Two things had to be found on the way. Memory is returned at a
declaration boundary only with `set_option Elab.async false`: with
asynchronous elaboration on, a 128-declaration file peaks at 5.2 GB, more
than its largest declaration needs, and `lean -j1` does not change that.
And a `def` of a few thousand gates needs `set_option maxRecDepth` or the
code generator gives up, which is what the old 80-qubit "definitions only"
error was.

**The tableau's cost is `2n · gates`, about 0.2 to 0.3 ms per generator and
gate, and re-synthesis of random circuits is what makes it large.** PyZX's
`full_reduce` returns the dense canonical form of a generic Clifford, about
`1.5 n²` gates (597, 2346 and 8261), so the random rungs cost 4.6 s, 39 s
and 422 s. Structured circuits do not blow up: a round of surface-code
syndrome extraction on 161 qubits goes from 368 to 436 gates and certifies
in 39 s at 2.1 GB, a 200-qubit GHZ ladder in 12 s, and the two-round
circuit on 97 qubits, which PyZX reduces to the *empty* circuit because the
`X` and `Z` extraction circuits commute, is certified equal to nothing in
12 s. At these sizes memory stays at the imports. The remaining lever for
the tableau is time: all `2n` generators walk the circuit separately, and
a column-packed tableau (one `Nat` per bit matrix, a gate a few shifts and
xors, as the phase polynomial's packed rows) would make the cost `gates`
instead of `2n · gates`, an estimated factor of sixty at 80 qubits
(`QUEUE.md`).

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
on `check` and on the two forms is the way to see it. For the tableau the
script's Python mirror answers the same question before Lean runs.

## Where each tool stands

| Tool | Relation | Cost, measured | Reach on this machine |
|---|---|---|---|
| Phase polynomial | `≡ᵤ`, and `¬ ≡ᵤ` | 0.2 ms per CNOT; up to 10 ms per phase gate on a dense 80-wire parity | 80 qubits, 800 gates in 4 s; no chunking needed |
| Tableau, chunked | `≡ₛ` | 0.2 to 0.3 ms per generator and gate | 80 random qubits (8261 gates) in 7 min; 161 structured qubits in 39 s |
| Basis decide, chunked | `≡ᵤ`, `≡ₚ` | 0.6 s and 165 MB per basis vector at 7 qubits, 32 gates | 7 qubits in 78 s; `gates · 4^n` scaling puts 8 qubits at minutes, 10 at hours |
| Certificate replay | `≡ᵤ` | not rerun here | about 150 gates, bound by replay memory (`QUEUE.md`, item 1) |

## Reproduce

```bash
PY=/tmp/circuiteq-pyzx-venv/bin/python
$PY scripts/scale_test.py --family clifford --sizes 20 40 --chunk 8 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
$PY scripts/scale_test.py --family clifford --sizes 80 --chunk 4 --timeout 2400 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
$PY scripts/scale_test.py --family ghz --sizes 50 100 200 --chunk 16 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
$PY scripts/scale_test.py --family surface --rounds 1 --sizes 5 7 9 --chunk 8 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
$PY scripts/scale_test.py --family surface --pipeline basic --sizes 3 5 7 --chunk 8 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
$PY scripts/scale_test.py --family cnot_t --sizes 10 20 40 80 \
  --workdir /tmp/scale --results benchmarks/scale/results.json
python3 scripts/chunked_decide.py SteanePlus --chunk 1 --workdir /tmp/chunked
```
