# Milestone 1 and 3: equivalence checker measurements

Status: stopped at the user's request; partial results only. No further checks are queued.

Exact TZAP -O1 pairs from the accepted Lean harness runs. Milestone 1 has
48 qubits and 4,459/2,703 gates; milestone 3 has 192 qubits and
70,075/41,547 gates. Both Lean runs were independently accepted.

Each checker receives one hour and 16 GiB of sampled process-tree RSS.
Checks run sequentially. Time includes imports and circuit loading.
RSS is sampled every 0.25 seconds, so short peaks can be missed.
The deadline uses calendar wall time, including system sleep. An earlier
attempt used the macOS monotonic clock and was discarded without a
verdict; its logs remain under interrupted-attempts/monotonic-clock.

| Milestone | Checker | Verdict | Wall seconds | Peak RSS GiB |
|---|---|---|---:|---:|
| 1 | qcec | timeout | 3600.029 | 1.7775 |
| 1 | qcec_dd | timeout | 3600.215 | 1.7766 |
| 1 | pyzx | cancelled_by_user | 157.327 | — |

Versions and machine details: `environment.json`. Exact pairs, QASM hashes,
commands, complete stdout/stderr and per-run results are saved beside this report.

Feynman feynver is not installed (nor is a Haskell toolchain); it is
recorded as not run, not as a failed checker. No additional applicable
checker was installed in the benchmark environment.

QCEC uses the existing hard_pair.py default-portfolio and alternating-DD
configurations. PyZX uses verify_equality; false means inconclusive.
The configured QuiZX modes, full_simp and full_simp plus stabilizer
decomposition of the closed miter, were not run on either pair.

A successful external checker result means this pair does not meet the
milestone requirement that every published checker fail. Unavailable tools
and inconclusive runs do not establish that requirement either.

The PyZX attempt was cancelled by the user, not completed or failed.
The remaining QuiZX checks and all milestone 3 checks were not run.

System sleep may have reduced the compute time available within the scored
calendar hours; awake time was not separately measured. These are observed
calendar-deadline timeouts, not evidence of failure after a full hour of CPU
execution. No complete cross-tool comparison can be inferred from them.

`results.jsonl` and `milestone-1/` preserve the result records, commands,
exact inputs and output logs for the three attempts. The output logs are
empty: no worker verdict was emitted before termination. Recorded absolute
paths identify the original environment and need adapting on another machine.
The discarded attempt remains archived locally and is not scored here.
