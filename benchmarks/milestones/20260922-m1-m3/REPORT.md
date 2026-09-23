# Milestone 1 and 3: equivalence checker measurements

Status: running; results below are partial.

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

Versions and machine details: `environment.json`. Exact pairs, QASM hashes,
commands, complete stdout/stderr and per-run results are saved beside this report.

Feynman feynver is not installed (nor is a Haskell toolchain); it is
recorded as not run, not as a failed checker. No additional applicable
checker was installed in the benchmark environment.

QCEC uses the existing hard_pair.py default-portfolio and alternating-DD
configurations. PyZX uses verify_equality; false means inconclusive.
QuiZX full_simp is measured separately from full_simp plus stabilizer
decomposition of the closed miter. The latter compares the squared trace
magnitude to 4^n using Scalar.is_one, without a tolerance.

A successful external checker result means this pair does not meet the
milestone requirement that every published checker fail. Unavailable tools
and inconclusive runs do not establish that requirement either.
