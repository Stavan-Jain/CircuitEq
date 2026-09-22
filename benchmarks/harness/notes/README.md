# Notes: what external optimisers do to our circuits

Measurements behind the harness's task design (19 September 2026). The
question: our first large pair, `peephole_8q_1000g_s1`, was made by a
peephole pass that uses exactly the library's own commutation rules
(`scripts/peephole_pairs.py`), so a proof inside the library's vocabulary
exists by construction. What do real optimisers do to the same circuit, and
how far are their outputs from what the library can prove today?

## The tools

- **PyZX 0.9.0**, in the virtualenv `~/.circuiteq-harness/envs/pyzx` (with
  numpy; `benchmarks/circuits/README.md`, "Reproduce", has the install),
  through `optimize` in `scripts/check_pyzx_benchmarks.py`: `teleport`
  (`teleport_reduce`, then `basic_optimization`) and `full_reduce` (with
  extraction, then `basic_optimization`).
- **TZAP 0.6.1** (`github.com/qqq-wisc/tzap`, Apache-2.0), the PyPI wheel
  installed without its optional Qiskit and PennyLane dependencies:

  ```bash
  python3 -m venv ~/.circuiteq-harness/envs/tzap
  ~/.circuiteq-harness/envs/tzap/bin/python -m pip install --no-deps tzap==0.6.1
  ~/.circuiteq-harness/envs/tzap/bin/tzap in.qasm -o out.qasm -O2 --decompose-rz --decompose-cz
  ```

  Levels `-O1`, `-O2`, `-O3`, `-Osuper`. It reads OpenQASM 2 with
  `h x z s sdg t tdg rz cx cz ccx ccz`; it has no `y`, so a `Y q` is written
  `sdg q; x q; s q`, which is exact. With the two `--decompose` flags the
  output uses `cx h s sdg t tdg x z` only. Delete the directory to remove it.

Neither tool's gate set has `Y`; both translations above are exact, and
every output below was compared with the original as a full unitary.

## The 1000-gate circuit (8 qubits, T-count 257, 323 CX, 150 H)

"Diff-matched" is how many of the original's gates a diff matches after both
lists are put in one canonical order under the library's commutations. A
segment is a stretch between two points where the two circuits' states
agree up to a global phase; cutting there is how the agent proved the
peephole pair. "Longest" counts the gates of both sides.

| twin | time | gates | T | CX | relation | diff-matched | segments | longest |
|---|---|---|---|---|---|---|---|---|
| our peephole pass | 0.07 s | 752 | 127 | 301 | exact | 666/1000 | 596 | 113 |
| TZAP `-O1` | 0.03 s | 736 | 101 | 301 | up to phase | 570/1000 | 118 | 443 |
| TZAP `-O2` | 0.12 s | 660 | 101 | 289 | up to phase | 477/1000 | 76 | 1045 |
| TZAP `-O3` | 0.04 s | 651 | 101 | 288 | up to phase | 466/1000 | 80 | 1023 |
| TZAP `-Osuper` | 13.8 s | 647 | 101 | 285 | up to phase | 442/1000 | 64 | 1084 |
| PyZX `teleport` | 0.1 s | 679 | 109 | 276 | up to phase | 104/1000 | 3 | 1675 |
| PyZX `full_reduce` | 0.1 s | 797 | 101 | 351 | up to phase | 67/1000 | 2 | 1795 |

- Every real optimiser's output is equal to the original only **up to a
  global phase** (for TZAP `-O1` the original is `ω¹` times the output).
  When this was measured (library `a9a80ed`) the library could not compose
  proofs of `≡ₚ`; from `83cc1d7` it can (`PLAYBOOK.md`, entry 8), and since
  `(SH)³ = ω·I`, `equivalentWithPhase_iff_phaseGadget` turns any of these
  pairs into an exact one against `optimized ++ phaseGadget k i` at no
  T-cost.
- TZAP at its lightest level is the next rung after our peephole pass: it
  keeps the skeleton (570 of 1000 gates match), but its merges act on
  parities across CNOTs, so the pair cuts into 118 segments of which five
  hold 673 of the 1000 original gates (69, 81, 126, 140 and 257 gates).
  Those need phase-polynomial reasoning across Hadamards (`QUEUE.md`, the
  Hadamard-variable item), or cut points that hold up to a residual.
- PyZX's output, even from the pipeline that keeps the skeleton on
  structured circuits, is a different gate list on this random circuit: a
  diff matches a tenth of it and there is nowhere to cut. Brute force on the
  whole register would be 110 M amplitude steps: hours, and about 17 GB
  retained per basis vector.

## Two structured circuits (5 qubits)

| circuit | T-count | PyZX teleport | PyZX full_reduce | TZAP (any level) | TZAP output |
|---|---|---|---|---|---|
| `tof_3` (45 gates) | 21 | 19 | 15 | 15 | exact, 38 gates at `-O2` |
| `barenco_tof_3` (60 gates) | 28 | 24 | 16 | 16 | exact, 42 gates at `-Osuper` |

Here TZAP's output is exactly equal, and at five qubits the pairs are within
reach of the whole-register basis decide. Both are harness tasks
(`tof_3_tzap`, `barenco_tof_3_tzap`), and both were certified through the
harness's judge with `by decide +kernel` (restatement, the three standard
axioms, kernel replay; 24 s and 26 s), by hand with `setup` and `./submit`
rather than in a recorded run, so `results.jsonl` has no row for them:
T-count 15 and 16, against the 19 and 24 of the promoted benchmarks. They do
not cut into segments either (the
longest segment spans most of the pair), so the same circuits at larger
sizes need the Hadamard-variable form.

## Reproducing

The scripts that first made these measurements (`optimisers.py`,
`distance.py` and `tzap_probe.py`, once in this directory) were folded into
`scripts/circuit_pairs.py`, whose `probe` prints the same table for one
circuit: the twins it makes itself (the peephole pass, both PyZX pipelines,
TZAP at `-O2`) and any ready-made twin given with `--against`. Segments are
found through random projections of the prefix states rather than the
states themselves, so those columns agree with the tables above up to
chance.

```bash
PY=~/.circuiteq-harness/envs/pyzx/bin/python
python3 scripts/peephole_pairs.py --qubits 8 --gates 1000 --seed 1 --out pair.json
$PY scripts/circuit_pairs.py probe pair.json                  # peephole, PyZX x2, TZAP -O2
CIRCUITEQ_TZAP_ARGS="-Osuper --decompose-rz --decompose-cz" \
  $PY scripts/circuit_pairs.py probe pair.json --twin tzap    # TZAP at another level
$PY scripts/circuit_pairs.py probe pair.json --twin --against out.qasm   # a twin made elsewhere
```
