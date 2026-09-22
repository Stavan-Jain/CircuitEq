# A pair past every published checker

`scripts/hard_pair.py` builds a Clifford+T pair designed to push every family
of equivalence checker past its published limit at once, and runs a ladder of
sizes through the checkers that install locally. The survey behind the design
is `docs/tool-survey.md` (section 7).

## The pair

- **A**: `n` rounds on `n` wires. A round is a CX on every pair of a random
  perfect matching (random orientation), then on every wire one of H, S, T or
  Tdg, or nothing, with probability 1/4 each.
- **B**: the same unitary up to a global phase, in Pauli-rotation form. Every
  T of A is pushed to the front through the Clifford gates before it, with a
  tableau that keeps exact signs (`A = D · R_m ⋯ R_1`); `⌈5n/8⌉` spider nests
  are inserted (15 rotations of angle `±π/8` about the nonempty products of 4
  commuting Paulis, signs `(-1)^(|S|+1)`, whose product is a global phase);
  rotations about equal Paulis are merged through commuting neighbours and
  commuting neighbours are shuffled; each rotation is emitted as a basis
  change, a CNOT ladder, a phase and the inverses, and `D` is re-synthesised
  from its tableau by elimination. B shares no gate positions with A.
- **B-** (dense mutant): B with one nest rotation negated, one with X or Y on
  some wire, from the second half of B. It differs from B in one gate and is
  not equivalent to A.
- **B-diag** (diagonal mutant): B with a diagonal rotation negated that has
  only diagonal rotations before it, so the difference is a diagonal phase no
  computational-basis stimulus can see. It exists only when B begins with a
  diagonal rotation of odd phase (here at 8 and 12 qubits).

Every step is an exact identity. `--self-test` (CI) checks A ≡ B, A ≢ B- and
A ≢ B-diag on dense unitaries from 4 to 7 qubits, that B-diag's difference is
diagonal, and, when PyZX is importable, that PyZX reads A and B as one
unitary. Generation is deterministic in the seed; `meta.json` records the
SHA-256 of every file.

Why each family should fail: A's rounds make the unitary dense and B's gate
order unrelated to A's (decision diagrams, windows, alignment); the nests are
identities that no ZX rule removes, so the ZX checkers stay inconclusive and
leave hundreds of non-Clifford spiders (stabiliser decomposition); B's
Hadamards are basis changes of dense rotations with no counterpart in A (path
sums); all-to-all CNOTs give treewidth about `n` (tensor networks, model
counting); and at 64 qubits no single input can be simulated.

## Checkers

Each check runs in a child process under a 300 s wall-clock limit and a 6 GB
resident-memory watchdog. A checker that runs out of time or memory at one
size is skipped above it, for that pair.

| Checker | What runs |
|---|---|
| `dense` | numpy unitaries, compared up to global phase; to 12 qubits, since a unitary is 4ⁿ·16 bytes (68 GB at 16) |
| `stimuli` | numpy state vectors on up to 16 random products of single-qubit stabiliser states; fidelity below `1 − 1e-8` refutes |
| `pyzx` | PyZX 0.9.0 `Circuit.verify_equality` (`full_reduce` of the miter) |
| `quizx` | quizx 0.3.0 `full_simp` of the miter circuit A · B⁻¹, identity test on the result; reports the residual spiders and non-Clifford phases |
| `qcec` | MQT QCEC 3.10.0, default configuration (alternating DD, simulation and ZX in parallel), its timeout set to the limit |
| `qcec_dd` | QCEC, alternating DD checker only |
| `qcec_zx` | QCEC, ZX checker only |
| `qcec_sim` | QCEC, simulation checker only (16 computational-basis stimuli) |

## Results (22 September 2026, seed 1, Apple M4, 16 GB)

The ladder of this commit covers 8 to 16 qubits. The run continues to 24
qubits, where the stimulus evidence should give out, and its results follow
in the next commit. Larger rungs are not run: every checker that can prove
equivalence has failed by 16 qubits, a larger pair can only be harder, and at
32 a state vector alone is 64 GB. Each cell is the verdict on A against B, B- and B-diag, in that
order: decided correctly (✓), right but only evidence (≈), no answer (?), a
wrong indication (✗), out of time (T) or memory (M), not run (·).

| Qubits | Rounds | Nests | A: gates / CX / H / T / depth | B: gates / CX / H / T | Rotations (median weight) |
|---:|---:|---:|---|---|---|
| 8 | 8 | 5 | 80 / 32 / 14 / 20 / 16 | 877 / 528 / 180 / 59 | 67 (5) |
| 12 | 12 | 8 | 173 / 72 / 35 / 33 / 24 | 1678 / 1005 / 372 / 71 | 90 (6) |
| 16 | 16 | 10 | 331 / 128 / 72 / 63 / 32 | 5097 / 2963 / 1327 / 129 | 147 (12) |

| Checker | n = 8 | n = 12 | n = 16 |
|---|---|---|---|
| `dense` | ✓ ✓ ✓ | ✓ ✓ ✓ | · · |
| `stimuli` | ≈ ✓ ✓ | ≈ ✓ ✓ | ≈ ✓ |
| `pyzx` | ? ? | ? ? | ? ? |
| `quizx` | ? ? | ? ? | ? ? |
| `qcec` | ? ✓ ? | ? ✓ ? | T T |
| `qcec_dd` | ✓ ✓ ✓ | ✓ ✓ ✓ | T, mutant pending |
| `qcec_zx` | ✗ ≈ | ✗ ≈ | pending |
| `qcec_sim` | ≈ ✓ ✗ | ≈ ✓ ✗ | pending |

What the small rungs already show:

- **The ZX checkers never prove the pair**, at any size: PyZX and quizx are
  inconclusive from 8 qubits, and quizx leaves 57, 90 and 154 non-Clifford
  spiders at 8, 12 and 16 qubits.
- **QCEC's ZX checker says "probably not equivalent" about the equivalent
  pair**, and the default portfolio, which runs it alongside the others,
  answers "no information" on A against B at 8 and 12 qubits and times out at
  16.
- **QCEC's simulation checker calls the diagonal mutant "probably
  equivalent"**, since computational-basis stimuli cannot see a diagonal
  phase; random stabiliser product states find it on the first try.
- **QCEC's DD checker is the one tool that decides every pair at 12 qubits**
  (3.6 s for the equal pair, 90 s to refute the diagonal mutant), and it runs
  out of time at 16 on the equal pair, at 0.16 GB: slow, not out of memory.
  At 16 qubits no checker proves A ≡ B; only the stimuli give evidence.

## Reproduce

The checkers need the harness env `envs/qcec` (see the script's docstring for
the `uv` commands); generation needs only the standard library.

```bash
PY=~/.circuiteq-harness/envs/qcec/bin/python
$PY scripts/hard_pair.py --self-test
$PY scripts/hard_pair.py make --n 64 --out /tmp/hp64      # one rung: QASM, rotations, meta
$PY scripts/hard_pair.py ladder --rungs 8,12,16,24,32,40,64 --timeout 300   # into ~/.circuiteq-harness/hard-pair
$PY scripts/hard_pair.py table                             # the tables above, from results.json
```
