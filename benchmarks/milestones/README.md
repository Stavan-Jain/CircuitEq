# Milestone equivalence experiments — draft

Two fresh GPT-6 Astra agents proved the fixed TZAP `-O1` pairs below using
CircuitEq at `d7ddcf86dc2ca2185861c9a8c832a749a03af689`. Both submissions
and the separate final judges accepted their proofs, including axiom audits
and independent Lean kernel replay. The proofs derive exact unitary equality
and export the requested equivalence up to global phase.

| Candidate | Qubits | Gates, original → optimized | T/Tdg, original → optimized | First acceptance |
|---|---:|---:|---:|---:|
| 1: `gf2^16_mult` | 48 | 4,459 → 2,703 | 1,792 → 1,040 | 295 s |
| 3: `gf2^64_mult` | 192 | 70,075 → 41,547 | 28,672 → 16,448 | 1,059 s |

These are agent search-to-acceptance times, **not isolated kernel timings**.
Each agent had fresh context, the full library, a one-hour budget, and a
16 GiB per-Lean-process guard. Provenance documents and prior attempts were
withheld. Native-agent transcripts, token usage and aggregate peak memory
were not captured; unavailable measurements remain null in the result rows.
These pairs were held out for these runs; they now have published proofs.
Candidate 2 was not attempted.

## Proofs and fixed inputs

- Candidate 1: `../harness/tasks/milestone_gf2_16_mult_tzap_o1/`, with the
  accepted certificate and `judge.json` under
  `../harness/results/20260922-223918-2db1eb/`.
- Candidate 3: `../harness/tasks/milestone_gf2_64_mult_tzap_o1/`, with the
  accepted certificate and `judge.json` under
  `../harness/results/20260922-225611-73c7d3/`.
- `fixtures/milestone-{1,3}.json` contain the exact gate lists. Both twins
  were generated with TZAP 0.6.1 and
  `-O1 --decompose-rz --decompose-cz`. The original catalogue's `-O2` twins
  are unchanged. A hard-coded `-O2` display label in the catalogue helper's
  output was corrected in these fixture copies; the recorded options and
  every gate are unchanged.

The larger task uses named 256-gate chunks solely to bound input-file
elaboration. All 111,622 input instructions were compared with the source
pair. This setup ran before the agent's clock started.

The small proof normalizes 256 local Hadamard patterns and checks two
phase-polynomial blocks with a carried diagonal residual. The large proof
uses a generic three-wire identity, 127 kernel-checked block certificates,
residual composition, and exact reconstruction of both fixed circuits.
Generated certificate files are retained as experiment artifacts, not added
to the library umbrella or its trusted core. Candidate 1's judge warning is
an unimported `#eval` probe; its final proof uses `decide +kernel` and passed
independent replay. Candidate 3's judge reports no warnings. A full human
review of the generated certificates remains outstanding.

To replay a saved certificate, use the harness `prepare` and `setup`
commands from `../harness/README.md` at the recorded library commit. Select
the corresponding task from this checkout, then copy that run's saved
`Solution.lean` and `Solution/` modules into the newly prepared workspace.
Run `./submit equiv` there. Reuse already-built dependencies; do not fetch
or rebuild mathlib. The two saved solutions use the same namespace and must
be checked in separate harness workspaces.

## External-checker comparison is in progress

`20260922-m1-m3/REPORT.md` is the current partial snapshot. The draft does
**not** claim that either candidate defeats all other equivalence checkers.
The sequential batch is measuring QCEC 3.10.0's default portfolio and its
alternating DD checker, PyZX 0.9.0 `verify_equality`, QuiZX 0.3.0 `full_simp`,
and QuiZX's stabilizer decomposition of a closed miter. Each configuration
gets one hour and 16 GiB. Feynman is unavailable locally and must be recorded
as **not run**, not failed.

The runner is `../../scripts/milestone_checkers.py`. It currently expects
the two saved local harness runs under `~/.circuiteq-harness/runs/`; each
must contain its independently accepted `meta/judge.json` and exact
`meta/pair.json`. The committed proof records and fixtures preserve those
inputs. Use an environment with the versions in `environment.json`:

```sh
python scripts/milestone_checkers.py batch \
  --out benchmarks/milestones/20260922-m1-m3 \
  --seconds 3600 --memory-gib 16
```

Do not start a second batch while one is active. A file lock prevents
concurrent batches against the same output directory; completed rows are
skipped when resuming. Commands, QASM hashes and complete stdout/stderr are
saved locally. Volatile runtime files are excluded from this draft; completed
measurements and their logs will be added after the batch finishes.

Validation so far: 15 isolated positive, phase-equivalent and negative
controls passed across all five configurations; 12 seeded two-qubit
closed-miter tests agreed with dense matrices. A short deadline control
also passed. QuiZX's extra adapter closes the circuit miter and compares
its squared trace magnitude with `4^n` using the library's scalar equality.

An initial unscored QCEC attempt overran calendar time with a monotonic
clock and was archived locally without a verdict. The runner now enforces
a calendar deadline using `time.time`. System sleep can still reduce the
compute time available within that hour, and the timing conditions must be
reported when interpreting the final comparison. The discarded attempt
must not count as a checker failure.
