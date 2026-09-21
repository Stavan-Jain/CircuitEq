# Circuit catalogue: real Clifford+T circuits, as a ladder

Real circuits of increasing size, for the two tasks the library is built for
(`ROADMAP.md`, "Two products, one architecture"):

1. **Equivalence checking.** A pair of circuits, an original and an optimised
   twin, that an agent proves equal or refutes in Lean. The pairs made so far
   are under `pairs/`, with their difficulty numbers in `pairs/index.json`.
2. **Optimisation.** One circuit, which an agent must make cheaper (T-count
   first) with a Lean proof of equivalence. Here the source circuit is the
   benchmark; `optimization.json` lists the recommended ones per tier with the
   T-count that uncertified tools reach on the same gate list.

Until now the repository had five small promoted pairs, an eleven-circuit
survey and one synthetic pair of 1000 random gates whose twin is made with the
library's own commutation rules. This catalogue replaces "random" by circuits
other people wrote and other people's optimisers rewrote.

| File | What it is |
|---|---|
| `README.md` | this catalogue |
| `manifest.json` | the same, machine-readable: provenance, `sha256` of every source file and of every translated gate list, how each was verified, every refusal |
| `optimization.json` | source circuits for the optimisation task, with the tools' T-counts |
| `pairs/*.json` | the first batch of pairs, in the format of `agent_harness.py import-pair` |
| `pairs/index.json` | one row per pair made, in the repository or not, with its metadata |
| `LICENSES/` | the licence texts that redistribution of the derived gate lists requires |
| `scripts/circuit_sources.py` | fetch, translate, verify, write the manifest |
| `scripts/circuit_pairs.py` | make twins, measure them, write the pairs and `optimization.json` |

No circuit file of a third party is copied here. The fetch script downloads
them into `~/.circuiteq-harness/circuit-cache` at a pinned commit and checks
each against the `sha256` in the manifest; translation is deterministic, and
the manifest records the hash of every translated gate list, so two machines
can tell that they hold the same benchmark.

## The alphabet, and what "exact" means

The library's circuits are lists of `H X Y Z S Sdg T Tdg` on a wire and
`CX c t`. A source circuit enters the catalogue only if it is exactly
expressible in that alphabet, global phase included, by these rules
(`manifest.json`, `translation`):

- `cz a b` is `H b; CX a b; H b`; `swap a b` is `CX a b; CX b a; CX a b`.
- `ccx a b c` is the seven-`T` Toffoli of `qelib1.inc`, fifteen gates:
  `H c; CX b c; Tdg c; CX a c; T c; CX b c; Tdg c; CX a c; T b; T c; H c;
  CX a b; T a; Tdg b; CX a b`. `ccz` is the same without the two Hadamards;
  the `.qc` format's `Zd` (the inverse, which is the same operator) is that
  list reversed with every gate inverted. `cswap a b c` is `CX c b; ccx a b c;
  CX c b`. This is the decomposition of `scripts/tcount_survey.py` and of
  TZAP's own copy of the Feynman suite, so the original T-counts are the
  literature's (seven per Toffoli).
- `u1`, `p` and `rz` are accepted only at multiples of `π/4` and read as
  `diag(1, e^{ikπ/4})`, the `PHASES` table of
  `scripts/check_pyzx_benchmarks.py`. That is `qelib1.inc`'s and PyZX's `rz`.
  Qiskit's `rz(θ)` is `e^{-iθ/2}` times that, and for odd `k` the factor
  `e^{-ikπ/8}` is not even a power of `ω`, so a file that uses `rz` is
  flagged in the manifest (`rz_convention`). **No file in the catalogue
  contains `rz`, `u1` or `p`**; the only place the convention matters is
  PyZX's output, which is read as gate objects, never as QASM text.
- Gate definitions (`gate majority a,b,c { … }`) are expanded, several
  registers are laid out in declaration order, a gate on a whole register is
  broadcast.
- Dropped, because they do not change the operator, and counted per file
  (`dropped`): `barrier`, `id`, and **terminal measurements**. A measurement
  is terminal when no later gate touches its qubit; the benchmark is then the
  unitary part of the program, which is what an optimiser must preserve.
- Refused, with the reason recorded: any other gate or angle, `reset`,
  classical control (`if`), a gate on a qubit after it was measured, a gate
  with a repeated wire, `opaque` gates, OpenQASM 3.

Nothing is approximated. A rotation by `π/8` is a refusal, not a
Solovay–Kitaev sequence.

## How a translation is checked

Every circuit is parsed into *native* operations (a Toffoli is one
operation) and translated; the two are then compared numerically, global
phase included, with a small in-place numpy simulator
(`circuit_sources.py`, "Simulation"; qubit 0 is the most significant bit, as
in `tcount_survey.unitary`):

- **`unitary`**: up to 10 qubits the two full unitaries agree to `1e-9`.
- **`N random state(s)`**: up to 24 qubits both lists are applied to seeded
  random state vectors, while `gates · 2^n` stays under `6 · 10^10` (about
  two minutes; numpy moves some `5 · 10^8` amplitudes a second here).
- **`sparse simulation on 16 random basis inputs`**: beyond that. A
  Toffoli-based circuit keeps a basis state sparse (two terms inside a
  Toffoli), so both lists are applied to sixteen random basis inputs as
  dictionaries of amplitudes, at any width: 433 qubits, or the 514 412 gates
  of `hwb12`, take about a second. It samples sixteen columns of the
  operator, phases included, so it is weaker than a random state.
- **`gate bookkeeping only`**: where a basis input spreads over more than
  4096 basis states (a layer of Hadamards on many wires: `gf2^16_mult` and
  up, `qcla_adder_10`). Checked at every width: every gate is in the alphabet
  on distinct wires of the register, and the gate and `T` counts are what the
  per-gate rules predict. Each rule itself is verified in `--self-test` on
  every assignment of four wires, phase included, so such a translation is
  wrong only if the parser put a gate on the wrong wires, which the two
  independent readers below cover.
- **`identity translation`**: every source gate is already in the alphabet,
  so there is nothing to simulate.

Two independent readers cover the parser:

- **`= TZAP copy`**. TZAP ships its own pre-decomposed copy of the Feynman
  suite. For 41 of the 42 Feynman circuits here (TZAP leaves out `qft_4`) the
  translated gate list is identical to TZAP's file, gate for gate, at every
  width up to the 1 115 899 gates of `gf2^256_mult`. So what TZAP reports on
  its own benchmark files is about exactly these originals.
- **`PyZX parser agrees`**. Where pyzx is importable and the file is under
  2 MB, PyZX's QASM parser and PyZX's own Toffoli decomposition read the same
  file; the result is either the same gate list or, where it can be
  simulated, the same operator.

The generators are checked against their specifications as classical
functions on random inputs at any width (`tof`, `barenco_tof`: the target
flips iff all controls are set, dirty ancillas restored; `cuccaro`: the sum
and the carry), and against `tcount_survey.py`'s generators gate for gate.

## Sources

| Source | What | Commit | Licence | In this repository |
|---|---|---|---|---|
| `feynman` | [meamy/feynman](https://github.com/meamy/feynman), `benchmarks/qasm/` | `d2c382a` | BSD-3-Clause | derived gate lists in `pairs/`; licence text in `LICENSES/` |
| `qasmbench` | [pnnl/QASMBench](https://github.com/pnnl/QASMBench) | `357b942` | BSD-style (Battelle, 2020) | derived gate lists in `pairs/`; licence text in `LICENSES/` |
| `tzap` | [qqq-wisc/tzap](https://github.com/qqq-wisc/tzap), `benchmarks/` | `077b7a7` | Apache-2.0 | nothing (tier 4 only, and the cross-check) |
| `qec` | [Stavan-Jain/QECUnitaryCircuits](https://github.com/Stavan-Jain/QECUnitaryCircuits) | `3d96b5f` | none stated; this project's author | derived gate lists in `pairs/`; three files were already under `benchmarks/` |
| `pyzx_repo` | [zxcalc/pyzx](https://github.com/zxcalc/pyzx), `circuits/` | `ad022cf` | Apache-2.0 | PyZX's own published outputs, as twins in `pairs/`. **Not** the Nam et al. files (upstream [njross/optimizer](https://github.com/njross/optimizer) has no licence) nor the T-par outputs (a GPL-3.0 tool): fetched on demand, written to the cache only |
| `generated` | `scripts/circuit_sources.py` | — | this repository's | generated on demand |

Full commit hashes, the licence files' hashes and every file's `sha256` are
in `manifest.json`.

## The ladder

147 circuits in four tiers by size after translation: tier 1 up to 10 qubits
and 200 gates (48 circuits), tier 2 up to 30 qubits and 2000 gates (42), tier
3 up to 100 qubits and 20 000 gates (24), tier 4 beyond (33, to 1026 qubits
and 1 115 899 gates). 95 use the whole alphabet, 51 are Clifford only, and
one (`qec_rm15_1531_transversal_Tdg`) is in the `CX` plus diagonal fragment.
`Size` is the family's parameter; `Verified` is explained above. Rows are in
order of gate count (`scripts/circuit_sources.py catalogue --readme` rewrites
the tables from `manifest.json`).

<!-- BEGIN LADDER -->
### Tier 1

| Name | Family | Size | Qubits | Gates | T | H | CX | Fragment | Source | Verified |
|---|---|---:|---:|---:|---:|---:|---:|---|---|---|
| `qec_rep3_bitflip_encode` | qec_rep3 | 3 | 3 | 2 | 0 | 0 | 2 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_cat3_prep` | qec_cat | 3 | 3 | 3 | 0 | 1 | 2 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_cat_state_n4` | qb_cat | 4 | 4 | 4 | 0 | 1 | 3 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_qrng_n4` | qb_qrng | 4 | 4 | 4 | 0 | 4 | 0 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qec_cat4_prep` | qec_cat | 4 | 4 | 4 | 0 | 1 | 3 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_code_422_encode_00L` | qec_encoder | 4 | 4 | 4 | 0 | 1 | 3 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_deutsch_n2` | qb_deutsch | 2 | 2 | 5 | 0 | 3 | 1 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qec_rep3_phaseflip_encode` | qec_rep3 | 3 | 3 | 5 | 0 | 3 | 2 | Clifford | qec | identity translation; PyZX parser agrees |
| `gen_ghz_5` | gen_ghz | 5 | 5 | 5 | 0 | 1 | 4 | Clifford | generated | identity translation |
| `qec_cat5_prep` | qec_cat | 5 | 5 | 5 | 0 | 1 | 4 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_ghz5_fanout` | qec_ghz_fanout | 5 | 5 | 5 | 0 | 1 | 4 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_cat7_prep` | qec_cat | 7 | 7 | 7 | 0 | 1 | 6 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_steane_713_transversal_H` | qec_transversal | 7 | 7 | 7 | 0 | 7 | 0 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_steane_713_transversal_S` | qec_transversal | 7 | 7 | 7 | 0 | 0 | 0 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_teleportation_n3` | qb_teleportation | 3 | 3 | 8 | 1 | 4 | 2 | general | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_iswap_n2` | qb_iswap | 2 | 2 | 9 | 0 | 4 | 2 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_lpn_n5` | qb_lpn | 5 | 5 | 11 | 0 | 9 | 2 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qec_shor_913_encode` | qec_encoder | 9 | 9 | 11 | 0 | 3 | 8 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_steane_713_encode_0L` | qec_encoder | 7 | 7 | 12 | 0 | 3 | 9 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_grover_n2` | qb_grover | 2 | 2 | 16 | 0 | 10 | 2 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_toffoli_n3` | qb_toffoli | 3 | 3 | 18 | 7 | 2 | 6 | general | qasmbench | identity translation; PyZX parser agrees |
| `qec_steane_713_H_nf_fig4` | qec_encoder | 7 | 7 | 18 | 1 | 5 | 11 | general | qec | identity translation; PyZX parser agrees |
| `qasmbench_fredkin_n3` | qb_fredkin | 3 | 3 | 19 | 7 | 2 | 8 | general | qasmbench | identity translation; PyZX parser agrees |
| `qec_steane_713_encode_plusL` | qec_encoder | 7 | 7 | 19 | 0 | 10 | 9 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_adder_n4` | qb_adder | 4 | 4 | 23 | 8 | 2 | 10 | general | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_qec_en_n5` | qb_qec_en | 5 | 5 | 25 | 1 | 14 | 10 | general | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_hs4_n4` | qb_hs4 | 4 | 4 | 28 | 0 | 20 | 4 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qec_code_513_encode_0L` | qec_encoder | 5 | 5 | 31 | 0 | 20 | 7 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_simon_n6` | qb_simon | 6 | 6 | 44 | 14 | 10 | 14 | general | qasmbench | unitary; PyZX parser agrees |
| `gen_tof_3` | gen_tof | 3 | 5 | 45 | 21 | 6 | 18 | general | generated | unitary |
| `qec_code_833_encode_basis` | qec_encoder | 8 | 8 | 52 | 0 | 36 | 12 | Clifford | qec | identity translation; PyZX parser agrees |
| `feynman_tof_3` | tof | 3 | 5 | 57 | 21 | 18 | 18 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `gen_barenco_tof_3` | gen_barenco_tof | 3 | 5 | 60 | 28 | 8 | 24 | general | generated | unitary |
| `gen_cuccaro_2` | gen_cuccaro | 2 | 6 | 69 | 28 | 8 | 33 | general | generated | unitary |
| `feynman_barenco_tof_3` | barenco_tof | 3 | 5 | 76 | 28 | 24 | 24 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `feynman_mod5_4` | mod5 | 4 | 5 | 79 | 28 | 22 | 28 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `feynman_tof_4` | tof | 4 | 7 | 95 | 35 | 30 | 30 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `gen_tof_5` | gen_tof | 5 | 9 | 105 | 49 | 14 | 42 | general | generated | unitary |
| `qasmbench_error_correctiond3_n5` | qb_error_correctiond3 | 5 | 5 | 113 | 0 | 62 | 49 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `feynman_tof_5` | tof | 5 | 9 | 133 | 49 | 42 | 42 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `gen_cuccaro_4` | gen_cuccaro | 4 | 10 | 137 | 56 | 16 | 65 | general | generated | unitary |
| `qasmbench_adder_n10` | qb_adder | 10 | 10 | 142 | 56 | 16 | 65 | general | qasmbench | unitary; PyZX parser agrees |
| `feynman_barenco_tof_4` | barenco_tof | 4 | 7 | 146 | 56 | 42 | 48 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `feynman_mod_mult_55` | mod_mult | 55 | 9 | 147 | 49 | 42 | 48 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `qasmbench_sat_n7` | qb_sat | 7 | 7 | 180 | 70 | 29 | 60 | general | qasmbench | unitary; PyZX parser agrees |
| `gen_barenco_tof_5` | gen_barenco_tof | 5 | 9 | 180 | 84 | 24 | 72 | general | generated | unitary |
| `feynman_qft_4` | qft | 4 | 5 | 187 | 69 | 50 | 46 | general | feynman | unitary; PyZX parser agrees |
| `feynman_vbe_adder_3` | vbe_adder | 3 | 10 | 190 | 70 | 50 | 70 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |

### Tier 2

| Name | Family | Size | Qubits | Gates | T | H | CX | Fragment | Source | Verified |
|---|---|---:|---:|---:|---:|---:|---:|---|---|---|
| `qec_steane_713_transversal_CNOT` | qec_transversal | 14 | 14 | 7 | 0 | 0 | 7 | Clifford | qec | identity translation; PyZX parser agrees |
| `qec_rm15_1531_transversal_Tdg` | qec_transversal | 15 | 15 | 15 | 15 | 0 | 0 | CX+diagonal | qec | identity translation; PyZX parser agrees |
| `gen_ghz_20` | gen_ghz | 20 | 20 | 20 | 0 | 1 | 19 | Clifford | generated | identity translation |
| `qasmbench_cat_state_n22` | qb_cat | 22 | 22 | 22 | 0 | 1 | 21 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_ghz_state_n23` | qb_ghz | 23 | 23 | 23 | 0 | 1 | 22 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qec_rm15_1531_encode_0L` | qec_encoder | 15 | 15 | 32 | 0 | 4 | 28 | Clifford | qec | identity translation; PyZX parser agrees |
| `qasmbench_bv_n14` | qb_bv | 14 | 14 | 41 | 0 | 27 | 13 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_qec9xz_n17` | qb_qec9xz | 17 | 17 | 53 | 0 | 21 | 32 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_bv_n19` | qb_bv | 19 | 19 | 56 | 0 | 37 | 18 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `gen_surface_3` | gen_surface | 3 | 17 | 64 | 0 | 16 | 48 | Clifford | generated | identity translation |
| `qasmbench_bv_n30` | qb_bv | 30 | 30 | 78 | 0 | 59 | 18 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_multiply_n13` | qb_multiply | 13 | 13 | 98 | 42 | 12 | 40 | general | qasmbench | 2 random state(s); PyZX parser agrees |
| `gen_tof_8` | gen_tof | 8 | 15 | 195 | 91 | 26 | 78 | general | generated | 2 random state(s) |
| `feynman_csla_mux_3` | csla_mux | 3 | 15 | 210 | 70 | 60 | 80 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_barenco_tof_5` | barenco_tof | 5 | 9 | 218 | 84 | 62 | 72 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `feynman_rc_adder_6` | rc_adder | 6 | 14 | 244 | 77 | 66 | 93 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `gen_cuccaro_8` | gen_cuccaro | 8 | 18 | 273 | 112 | 32 | 129 | general | generated | 2 random state(s) |
| `qasmbench_bigadder_n18` | qb_bigadder | 18 | 18 | 284 | 112 | 32 | 130 | general | qasmbench | 2 random state(s); PyZX parser agrees |
| `feynman_gf2_4_mult` | gf2_mult | 4 | 12 | 289 | 112 | 78 | 99 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_hwb6` | hwb | 6 | 7 | 319 | 105 | 90 | 116 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `qasmbench_qram_n20` | qb_qram | 20 | 20 | 321 | 140 | 40 | 136 | general | qasmbench | 2 random state(s); PyZX parser agrees |
| `feynman_tof_10` | tof | 10 | 19 | 323 | 119 | 102 | 102 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_mod_red_21` | mod_red | 21 | 11 | 346 | 119 | 98 | 105 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `qasmbench_adder_n28` | qb_adder | 28 | 28 | 424 | 168 | 48 | 195 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `feynman_gf2_5_mult` | gf2_mult | 5 | 15 | 447 | 175 | 118 | 154 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `gen_cuccaro_14` | gen_cuccaro | 14 | 30 | 477 | 196 | 56 | 225 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_barenco_tof_10` | gen_barenco_tof | 10 | 19 | 480 | 224 | 64 | 192 | general | generated | 2 random state(s) |
| `feynman_csum_mux_9` | csum_mux | 9 | 30 | 532 | 196 | 140 | 168 | general | feynman | gate bookkeeping only; = TZAP copy |
| `feynman_ham15_low` | ham15 | low | 17 | 535 | 161 | 138 | 236 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_qcla_com_7` | qcla_com | 7 | 24 | 559 | 203 | 155 | 186 | general | feynman | 1 random state(s); = TZAP copy; PyZX parser agrees |
| `qasmbench_multiplier_n15` | qb_multiplier | 15 | 15 | 574 | 252 | 72 | 246 | general | qasmbench | 2 random state(s); PyZX parser agrees |
| `feynman_barenco_tof_10` | barenco_tof | 10 | 19 | 578 | 224 | 162 | 192 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_gf2_6_mult` | gf2_mult | 6 | 18 | 639 | 252 | 166 | 221 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `qasmbench_sat_n11` | qb_sat | 11 | 11 | 679 | 294 | 99 | 252 | general | qasmbench | 2 random state(s); PyZX parser agrees |
| `feynman_gf2_7_mult` | gf2_mult | 7 | 21 | 865 | 343 | 222 | 300 | general | feynman | 1 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_grover_5` | grover | 5 | 9 | 1023 | 336 | 334 | 288 | general | feynman | unitary; = TZAP copy; PyZX parser agrees |
| `feynman_qcla_mod_7` | qcla_mod | 7 | 26 | 1120 | 413 | 318 | 382 | general | feynman | sparse simulation on 16 random basis inputs; = TZAP copy; PyZX parser agrees |
| `feynman_adder_8` | adder | 8 | 24 | 1128 | 399 | 308 | 409 | general | feynman | 1 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_gf2_8_mult` | gf2_mult | 8 | 24 | 1139 | 448 | 286 | 405 | general | feynman | 1 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_gf2_9_mult` | gf2_mult | 9 | 27 | 1419 | 567 | 358 | 494 | general | feynman | sparse simulation on 16 random basis inputs; = TZAP copy; PyZX parser agrees |
| `feynman_ham15_med` | ham15 | med | 17 | 1600 | 574 | 492 | 534 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_gf2_10_mult` | gf2_mult | 10 | 30 | 1747 | 700 | 438 | 609 | general | feynman | sparse simulation on 16 random basis inputs; = TZAP copy; PyZX parser agrees |

### Tier 3

| Name | Family | Size | Qubits | Gates | T | H | CX | Fragment | Source | Verified |
|---|---|---:|---:|---:|---:|---:|---:|---|---|---|
| `qasmbench_cat_n35` | qb_cat | 35 | 35 | 35 | 0 | 1 | 34 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_ghz_n40` | qb_ghz | 40 | 40 | 40 | 0 | 1 | 39 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_cat_n65` | qb_cat | 65 | 65 | 65 | 0 | 1 | 64 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_ghz_n78` | qb_ghz | 78 | 78 | 78 | 0 | 1 | 77 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `gen_ghz_100` | gen_ghz | 100 | 100 | 100 | 0 | 1 | 99 | Clifford | generated | identity translation |
| `qasmbench_bv_n70` | qb_bv | 70 | 70 | 176 | 0 | 139 | 36 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `gen_surface_5` | gen_surface | 5 | 49 | 208 | 0 | 48 | 160 | Clifford | generated | identity translation |
| `gen_surface_7` | gen_surface | 7 | 97 | 432 | 0 | 96 | 336 | Clifford | generated | identity translation |
| `gen_tof_16` | gen_tof | 16 | 31 | 435 | 203 | 58 | 174 | general | generated | sparse simulation on 16 random basis inputs |
| `feynman_qcla_adder_10` | qcla_adder | 10 | 36 | 657 | 238 | 186 | 233 | general | feynman | gate bookkeeping only; = TZAP copy |
| `gen_barenco_tof_16` | gen_barenco_tof | 16 | 31 | 840 | 392 | 112 | 336 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_tof_32` | gen_tof | 32 | 63 | 915 | 427 | 122 | 366 | general | generated | sparse simulation on 16 random basis inputs |
| `qasmbench_adder_n64` | qb_adder | 64 | 64 | 988 | 392 | 112 | 455 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `gen_cuccaro_32` | gen_cuccaro | 32 | 66 | 1089 | 448 | 128 | 513 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_tof_50` | gen_tof | 50 | 99 | 1455 | 679 | 194 | 582 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_cuccaro_49` | gen_cuccaro | 49 | 100 | 1667 | 686 | 196 | 785 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_barenco_tof_50` | gen_barenco_tof | 50 | 99 | 2880 | 1344 | 384 | 1152 | general | generated | sparse simulation on 16 random basis inputs |
| `feynman_gf2_16_mult` | gf2_mult | 16 | 48 | 4459 | 1792 | 1086 | 1581 | general | feynman | gate bookkeeping only; = TZAP copy |
| `feynman_mod_adder_1024` | mod_adder | 1024 | 28 | 5425 | 1995 | 1710 | 1720 | general | feynman | sparse simulation on 16 random basis inputs; = TZAP copy; PyZX parser agrees |
| `qasmbench_multiplier_n45` | qb_multiplier | 45 | 45 | 5981 | 2646 | 756 | 2574 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `feynman_ham15_high` | ham15 | high | 20 | 6712 | 2457 | 2106 | 2149 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `qasmbench_multiplier_n75` | qb_multiplier | 75 | 75 | 17077 | 7560 | 2160 | 7350 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `feynman_gf2_32_mult` | gf2_mult | 32 | 96 | 17658 | 7168 | 4222 | 6268 | general | feynman | gate bookkeeping only; = TZAP copy |
| `feynman_hwb8` | hwb | 8 | 12 | 18220 | 5887 | 5046 | 7129 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |

### Tier 4

| Name | Family | Size | Qubits | Gates | T | H | CX | Fragment | Source | Verified |
|---|---|---:|---:|---:|---:|---:|---:|---|---|---|
| `qasmbench_ghz_n127` | qb_ghz | 127 | 127 | 127 | 0 | 1 | 126 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_cat_n130` | qb_cat | 130 | 130 | 130 | 0 | 1 | 129 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_ghz_n255` | qb_ghz | 255 | 255 | 255 | 0 | 1 | 254 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_cat_n260` | qb_cat | 260 | 260 | 260 | 0 | 1 | 259 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_bv_n140` | qb_bv | 140 | 140 | 352 | 0 | 279 | 72 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `qasmbench_bv_n280` | qb_bv | 280 | 280 | 712 | 0 | 559 | 152 | Clifford | qasmbench | identity translation; PyZX parser agrees |
| `gen_surface_9` | gen_surface | 9 | 161 | 736 | 0 | 160 | 576 | Clifford | generated | identity translation |
| `gen_ghz_1000` | gen_ghz | 1000 | 1000 | 1000 | 0 | 1 | 999 | Clifford | generated | identity translation |
| `qasmbench_adder_n118` | qb_adder | 118 | 118 | 1834 | 728 | 208 | 845 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `gen_surface_15` | gen_surface | 15 | 449 | 2128 | 0 | 448 | 1680 | Clifford | generated | identity translation |
| `gen_tof_100` | gen_tof | 100 | 199 | 2955 | 1379 | 394 | 1182 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_cuccaro_128` | gen_cuccaro | 128 | 258 | 4353 | 1792 | 512 | 2049 | general | generated | sparse simulation on 16 random basis inputs |
| `gen_barenco_tof_100` | gen_barenco_tof | 100 | 199 | 5880 | 2744 | 784 | 2352 | general | generated | sparse simulation on 16 random basis inputs |
| `qasmbench_adder_n433` | qb_adder | 433 | 433 | 6769 | 2688 | 768 | 3120 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `gen_cuccaro_512` | gen_cuccaro | 512 | 1026 | 17409 | 7168 | 2048 | 8193 | general | generated | sparse simulation on 16 random basis inputs |
| `tzap_cobble_t_laplacian_filter` | cobble | 11 | 11 | 34138 | 13442 | 13042 | 660 | general | tzap | identity translation; PyZX parser agrees |
| `feynman_gf2_64_mult` | gf2_mult | 64 | 192 | 70075 | 28672 | 16638 | 24765 | general | feynman | gate bookkeeping only; = TZAP copy |
| `tzap_cobble_t_matrix_inversion` | cobble | 12 | 12 | 82861 | 34423 | 24749 | 11985 | general | tzap | identity translation; PyZX parser agrees |
| `feynman_hwb10` | hwb | 10 | 16 | 91642 | 29939 | 25662 | 35170 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `tzap_cobble_t_chebyshev` | cobble | 14 | 14 | 112554 | 47894 | 31227 | 20459 | general | tzap | identity translation; PyZX parser agrees |
| `tzap_cobble_t_hamiltonian_simulation` | cobble | 16 | 16 | 226196 | 99219 | 52419 | 56764 | general | tzap | identity translation |
| `feynman_hwb11` | hwb | 11 | 15 | 256181 | 84196 | 72168 | 98023 | general | feynman | 2 random state(s); = TZAP copy; PyZX parser agrees |
| `feynman_gf2_128_mult` | gf2_mult | 128 | 384 | 279419 | 114688 | 66046 | 98685 | general | feynman | gate bookkeeping only; = TZAP copy |
| `tzap_qft_qft_q020_d32421` | synth_qft | 20 | 20 | 309835 | 167567 | 141858 | 410 | general | tzap | identity translation |
| `tzap_cobble_t_spectral_thresholding` | cobble | 16 | 16 | 309871 | 137061 | 67243 | 84506 | general | tzap | identity translation |
| `qasmbench_multiplier_n350` | qb_multiplier | 350 | 350 | 383844 | 170030 | 48580 | 165200 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `qasmbench_multiplier_n400` | qb_multiplier | 400 | 400 | 501877 | 222320 | 63520 | 216000 | general | qasmbench | sparse simulation on 16 random basis inputs; PyZX parser agrees |
| `feynman_hwb12` | hwb | 12 | 20 | 514412 | 171465 | 146970 | 191803 | general | feynman | sparse simulation on 16 random basis inputs; = TZAP copy |
| `tzap_qft_qft_q030_d50671` | synth_qft | 30 | 30 | 549880 | 297387 | 251578 | 915 | general | tzap | identity translation |
| `tzap_cobble_t_ols_ridge` | cobble | 22 | 22 | 587755 | 255692 | 140654 | 139716 | general | tzap | identity translation |
| `tzap_qft_qft_q040_d68921` | synth_qft | 40 | 40 | 790125 | 427207 | 361298 | 1620 | general | tzap | identity translation |
| `tzap_qft_qft_q050_d87171` | synth_qft | 50 | 50 | 1030570 | 557027 | 471018 | 2525 | general | tzap | identity translation |
| `feynman_gf2_256_mult` | gf2_mult | 256 | 768 | 1115899 | 458752 | 263166 | 393981 | general | feynman | gate bookkeeping only; = TZAP copy |
<!-- END LADDER -->

## Families, and how they scale

Families with a size parameter are the ladders: the largest rung solved is
the metric, because a fixed set saturates.

- **`tof`** (Feynman; `k` = 3, 4, 5, 10) and **`gen_tof`** (any `k`): a
  `k`-controlled NOT through `k − 2` clean ancillas, `2k − 3` Toffolis on
  `2k − 1` qubits. T-count `7(2k − 3)`. The generator emits `15(2k − 3)`
  gates; Feynman's files carry two cancelling Hadamard pairs around each
  Toffoli (`h; h; ccx; h; h` for the `.qc` file's `H; Z; H`), so
  `19(2k − 3)` gates.
- **`barenco_tof`** and **`gen_barenco_tof`**: Barenco et al., Lemma 7.2,
  with dirty ancillas, `4(k − 2)` Toffolis on `2k − 1` qubits, T-count
  `28(k − 2)`, `60(k − 2)` gates from the generator and about 72 per extra
  control in Feynman's files.
- **`gen_cuccaro`**: the Cuccaro ripple-carry adder on `k` bits, `2k + 2`
  qubits, `34k + 1` gates, T-count `14k`. `qasmbench_adder_n10` is this
  circuit at `k = 4` with five `X` gates of input preparation in front.
- **`qb_adder`** (QASMBench; `n` = 4, 10, 28, 64, 118, 433 qubits):
  ripple-carry adders with their input preparation; from 28 qubits on about
  `15.5 n` gates and `6.2 n` `T`. **`vbe_adder`,
  `rc_adder`, `adder_8`, `qcla_adder`, `qcla_com`, `qcla_mod`, `csla_mux`,
  `csum_mux`, `mod_adder`, `mod_mult`, `mod_red`, `mod5`** are the Feynman
  suite's single instances of other adders and modular arithmetic, 5 to 36
  qubits and 79 to 5425 gates.
- **`gf2_mult`** (Feynman; `k` = 4 to 10, 16, 32, 64, 128, 256):
  multiplication in GF(2^k), `3k` qubits, `k²` Toffolis, T-count `7k²`,
  about `17k²` gates: 289 gates at `k = 4`, 17 658 at 32, 1 115 899 at 256.
  The cleanest quadratic ladder here, and the one TZAP reports its scaling
  on.
- **`qb_multiplier`** (QASMBench; `n` = 15, 45, 75, 350, 400 qubits):
  integer multipliers, T-count about `1.4 n²`: 574 gates at 15 qubits,
  501 877 at 400.
- **`hwb`** (Feynman; 6, 8, 10, 11, 12 inputs): the hidden weighted bit
  function, synthesised; narrow and very deep, growing about fivefold per
  two inputs: 319 gates on 7 qubits, 18 220 on 12, 514 412 on 20.
  **`ham15`** (low, med, high: 535, 1600 and 6712 gates on 17 to 20 qubits),
  **`grover_5`**, **`qft_4`** (an approximate QFT already synthesised into
  Clifford+T) are single instances.
- **`cobble`** and **`synth_qft`** (TZAP's corpora): block-encoding circuits
  after Rz synthesis, 11 to 22 qubits and 34 138 to 587 755 gates, and
  synthesised QFTs on 20 to 50 qubits with 0.3 to 1.0 million gates, over
  half of which are `T`. Both are already in the alphabet, and as circuits
  they are exact whatever they approximate; tier 4.
- **Clifford-only ladders**, for the tableau checker: **`gen_ghz`**,
  **`qb_ghz`**, **`qb_cat`** (`n` gates on `n` qubits, to 1000),
  **`qb_bv`** (Bernstein–Vazirani, about `2.5 n` gates, to 280 qubits),
  **`gen_surface`** (two rounds of syndrome extraction of the rotated
  surface code of distance `d`, unitary part, `2d² − 1` qubits and
  `10d² − 8d − 2` gates; two identical rounds undo each other, so the whole
  circuit is the identity, which makes it a good target for "prove it equals
  `[]`"),
  and the **`qec_*`** encoders, cat states and transversal gates of
  QECUnitaryCircuits (3 to 15 qubits).

## Refused, and why

Recorded in `manifest.json` (`rejected`), by the parser or by the survey:

- **Feynman `mod_adder_1048576.qasm` and `cycle_17_3.qasm`** contain Toffolis
  whose target is one of their controls (`ccx q[48],q[29],q[48]`; 90 of the
  2470 Toffolis of the first file, 30 of the 677 of the second), which is not
  a gate of OpenQASM. The defect is in the `.qc` originals too (`Z 8 x22 8`;
  there a doubly-controlled `Z` with a repeated wire could be read as a `CZ`,
  but the `.qasm` that optimisers consume has no such reading). TZAP's copy
  decomposes them all the same, into 180 and 60 `cx` gates whose control is
  their target. Both files are out until upstream fixes them (the PyZX
  repository keeps a `cycle17_3-corrected.qc`).
- Feynman's `fprenorm.qc` has no `.qasm`, and `benchmarks/qasm3/` is
  OpenQASM 3 with loops, `reset` and measurement-controlled gates.
- **QASMBench**: every non-transpiled file under 1.5 MB went through the
  parser. 46 are in; refused were `ry`/`rx`/`u3`/`sx` rotations (dnn, knn,
  qugan, wstate, swap_test, QV, hhl, vqe, gcm, …), `rz`, `u1` and `cu1` at
  angles that are not multiples of `π/4` (ising, qaoa, vqe_uccsd, qft, qpe,
  pea, ipea, qf21), classical control (cc, inverseqft, qec_sm), `reset`
  (square_root, bwt, shor), and two files that act on a qubit after
  measuring it (`seca_n11`, `bb84_n8`). Fourteen files over 1.5 MB were not
  examined; every smaller member of their families is refused. The
  `*_transpiled.qasm` variants are in IBM's basis (`rz`, `sx`).
- TZAP's `cobble-rz` corpus has 122 to 910 unsynthesised `rz` rotations per
  circuit. The Nam et al. `QFT_and_Adders` and `PF` circuits use `QRot` at
  angles beyond `π/4`.
- RevLib was not fetched: no stable per-file URL or commit to pin and no
  licence statement; its `hwb`, `ham` and `cycle` functions are covered by
  the Feynman suite's copies.

## Pairs: the first batch

`scripts/circuit_pairs.py` pairs a catalogue circuit with a twin and writes
the JSON that `scripts/agent_harness.py import-pair` reads (and
`scripts/optimizer_harness.py import-pair`, which keeps the original and
files the twin as a baseline under `source.optimiser`). Four kinds of twin:

- **`peephole`**: the pass of `scripts/peephole_pairs.py`, exact by
  construction. This is the biased twin, made with the library's own rules;
  it is here as the easy end of the scale, now on real circuits.
- **`pyzx_teleport`**, **`pyzx_full_reduce`**: the two pipelines of
  `scripts/check_pyzx_benchmarks.py` (pyzx 0.9.0), each in a child process
  stopped at 240 s, and not started past 8000 gates (`hwb8`, 18 220 gates,
  did not finish either pipeline in 200 s). `Y` goes to PyZX as `Sdg; X; S`.
- **`tzap`**: TZAP 0.6.1 ([qqq-wisc/tzap](https://github.com/qqq-wisc/tzap),
  Apache-2.0; the install is in `benchmarks/harness/notes/README.md`) at
  `-O2` with its `rz` and `cz` decomposed, run on the circuit as OpenQASM in
  the alphabet's own gates (`Y` written `sdg; x; s`, exact) and read back
  with the catalogue's parser. Linear in the gate count, about a second per
  million gates, so it is the one twin made for every T-bearing circuit,
  tier 4 included. Its benchmark copies of the Feynman suite are these gate
  lists exactly, so what it reports on its own files is about these
  originals.
- **`nam_light`**, **`nam_heavy`**, **`tpar`**, **`pyzx_published`**: outputs
  that other people published for the Feynman suite, kept in the PyZX
  repository: Nam, Ross, Su, Childs and Maslov's optimiser, T-par, and PyZX
  itself. These are the pairs the project is about: a derivation between
  fixed endpoints that an optimiser discarded. Before pairing, the published
  input is checked to be the catalogue's circuit, by a normal form of the
  native operations (a Toffoli as `H; CCZ; H`, Hadamard pairs cancelled,
  commuting operations ordered). 27 of the 28 inputs are the Feynman files
  exactly; **`qcla_adder_10` is not**: Nam et al.'s input has one CNOT on the
  other side of a Hadamard, so its four pairs use the published input itself
  as the original.

390 pairs were made (`pairs/index.json`, and as a table in
`pairs/README.md`; fourteen more rows are runs that were skipped or stopped);
141 are in the repository (2.6 MB): the four twins of 29 circuits across
tiers 1 to 3, less two PyZX runs past the gate bound, and PyZX's published
output for 27 circuits. The rest are in the cache only: the Nam and T-par
pairs, whose sources have no clear licence to redistribute, and the PyZX and
TZAP runs on the other T-bearing circuits, made for `optimization.json`.

For each pair the index records what `describe` in `scripts/circuit_pairs.py`
measures (`probe FILE` prints the same for one circuit and its twins, which
is how the tables of `benchmarks/harness/notes/README.md` are reproduced
now): the relation that holds numerically (full
unitaries to 10 qubits, random states to 24, sixteen random basis inputs
beyond, marked `sampled`; an untrusted oracle throughout), gate, `T`, `H` and
`CX` counts, the share of the original's gates a diff matches, raw and after
both lists are put in one canonical order under `Instr.CanCommute`, and the
number of segments and the longest segment between points where the two
prefix states agree up to a phase. Prefix states are compared through four
random projections, not stored, which takes the segmentation to 20 qubits;
it was skipped on 152 pairs wider or longer than that, and the diff on 30
pairs past some 5500 gates a side. Medians over the pairs of each kind:

| Twin | Pairs | Diff, raw | Diff, canonical | Segments | Longest segment, share of the pair |
|---|---:|---:|---:|---:|---:|
| `peephole` | 29 | 0.73 | 0.75 | 180 | 0.01 |
| `pyzx_teleport` | 77 | 0.34 | 0.70 | 28 | 0.53 |
| `tzap` | 99 | 0.56 | 0.56 | 8 | 0.92 |
| `pyzx_published` | 28 | 0.34 | 0.49 | 5 | 0.93 |
| `nam_light`, `nam_heavy` | 56 | 0.43 | 0.47 | 3 | 0.97 |
| `pyzx_full_reduce` | 73 | 0.08 | 0.09 | 2 | 1.00 |
| `tpar` | 28 | 0.05 | 0.06 | 1 | 1.00 |

That is the ladder's second axis. A peephole twin cuts every few gates. Phase
teleportation keeps the skeleton, the diff finds 70 % of it once commuting
gates are ordered, and half of a typical pair is still one segment. TZAP's
`-O2` output sits between that and the published outputs: a diff on the lists
as they are matches more of it (56 % against 35 %), ordering commuting gates
adds nothing, and the longest segment spans 92 % of a typical pair. What
other people's optimisers published cuts hardly at all: the cut-and-window
recipe of the playbook has nothing to hold on to, and those are the real
pairs.

### What the batch found

- **PyZX's output is usually equal exactly, not only up to a phase.** Of the
  150 PyZX twins, 96 are exact and 23 more are exact on every sampled input;
  19 could not be checked (wide registers with Hadamard layers). Twelve are
  equal only up to a phase: `ω⁴ = −1` ten times (`sat_n7`, `qram_n20`,
  `hwb6`, `qcla_mod_7`, `bigadder_n18`, `sat_n11`, `ham15-high`,
  `adder_n118`), `ω⁷` once (`teleportation_n3`, full_reduce) and `ω` once
  (`adder_n28`, full_reduce, sampled). Those tasks state `≡ₚ`; all others
  state `≡ᵤ`. Nothing was found unequal, so no convention bug in the
  translation to and from PyZX.
- **One published output is wrong.** Nam et al.'s heavy output for
  `qcla_mod_7` (T-count 235, against 237 for the light one) is not
  equivalent to its input: on about half of all basis inputs the original
  returns a basis state and the heavy output a superposition of two. The
  light output and PyZX's agree with the original on the same inputs. At 26
  qubits this is a refutation task well past one basis vector in the kernel.
- **T-par's published outputs are mostly not unitarily equal to their
  inputs.** Of 28, 8 are exact and 4 could not be checked. 16 differ. Nine of
  those agree with the original on every input whose ancillas (the wires
  outside the `.qc` file's `.i` line) start in `|0⟩`: `tof_4`, `tof_5`,
  `tof_10`, `csla_mux_3`, `gf2^4` and `gf2^6` to `gf2^9`. That is T-par's
  contract, and it is none of `≡ᵤ`, `≡ₚ`, `≡ₛ`. The other seven
  (`rc_adder_6`, `adder_8`, `mod_mult_55`, `mod_red_21`, `gf2^5_mult`,
  `qcla_com_7`, `qcla_mod_7`) differ there too; in `rc_adder_6`,
  `mod_red_21` and `gf2^5_mult` a basis input with clean ancillas goes to
  another basis state. Each file's header records the gate counts of its
  input, which are those of the Feynman file, and the wire order is the
  same; six of the seven contain `X` gates, which only one of the agreeing
  circuits does. Whether T-par mishandled them or was run on another
  revision of the circuits was not found out. All 16 are `not_equiv` tasks
  made by a real tool.
- **`full_reduce` does not always reduce.** It takes the T-count of
  `gf2^16_mult` from 1792 to 1040 (teleport: 1536) and its 4459 gates to
  12 235; the 1455 gates of `gen_tof_50` become 1882.
- **TZAP's output is equal up to a global phase, and every power of `ω`
  occurs.** Of its 99 twins (every T-bearing circuit, tier 4 included, and
  the first batch's Clifford circuits), 68 are exact, 11 are equal up to a
  power of `ω` and 20 could not be checked (the wide registers with Hadamard
  layers); none was found unequal. `ω` on `hwb8`, `ω²` on `qft_4` and
  `grover_5`, `ω³` on `hwb11` and `spectral_thresholding`, `ω⁴` on
  `adder_8` and `sat_n11`, `ω⁵` on `mod_mult_55`, `ω⁶` on `adder_n4` and
  `matrix_inversion`, `ω⁷` on `hamiltonian_simulation`: those tasks state
  `≡ₚ`. It never made a T-count worse; the median twin has 57 % of the
  original's `T` gates and 67 % of its gates. TZAP itself took under 5 s on
  any circuit, the QASM round trip included, and 34 s on all 99 (the
  1 115 899 gates of `gf2^256_mult` in 1.5 s); the batch's seven minutes went
  into measuring the pairs in Python. Its `-O2` keeps less of the skeleton
  than phase teleportation does (the medians above), so these pairs, too,
  need the Hadamard-variable form (`QUEUE.md`, item 4) or cut points that
  hold up to a residual.

### The handful imported as harness tasks

`scripts/circuit_pairs.py handful` prints the commands; ten tasks were
imported under `benchmarks/harness/tasks/`, all `held-out` (no proof of them
exists in the repository or its history):

| Task | Qubits | Gates | T | States | Diff, canonical | Segments, longest | Why |
|---|---:|---:|---:|---|---:|---|---|
| `feynman_tof_5__pyzx_teleport` | 9 | 133 → 110 | 49 → 43 | `≡ᵤ` | 0.75 | 94, 12 | phase folding on a kept skeleton |
| `feynman_mod5_4__pyzx_full_reduce` | 5 | 79 → 30 | 28 → 8 | `≡ᵤ` | 0.08 | 1, 109 | a re-synthesis, small enough to brute-force |
| `qasmbench_adder_n10__peephole` | 10 | 142 → 138 | 56 → 48 | `≡ᵤ` | 0.94 | 138, 3 | ten qubits, exact by construction |
| `feynman_vbe_adder_3__pyzx_published` | 10 | 190 → 115 | 70 → 24 | `≡ᵤ` | 0.43 | 5, 295 | a published output; hardly cuts |
| `qasmbench_sat_n7__pyzx_teleport` | 7 | 180 → 167 | 70 → 62 | `≡ₚ` | 0.56 | 6, 337 | equal only up to `−1` |
| `feynman_rc_adder_6__pyzx_teleport` | 14 | 244 → 195 | 77 → 59 | `≡ᵤ` | 0.55 | 31, 367 | tier 2, past a basis decide |
| `feynman_gf2_4_mult__pyzx_published` | 12 | 289 → 199 | 112 → 68 | `≡ᵤ` | 0.60 | 11, 429 | published, tier 2 |
| `feynman_grover_5__peephole` | 9 | 1023 → 769 | 336 → 296 | `≡ᵤ` | 0.73 | 393, 512 | the 1000-gate rung, on a real circuit |
| `gen_tof_50__pyzx_teleport` | 99 | 1455 → 1601 | 679 → 583 | `≡ᵤ` (sampled) | 0.90 | not computed | width: 99 qubits |
| `feynman_hwb8__peephole` | 12 | 18 220 → 14 077 | 5887 → 5437 | `≡ᵤ` | not computed | 14 075, 10 | depth: the top rung |

The refutation tasks made by real tools (`feynman_qcla_mod_7__nam_heavy`, the
T-par pairs) are in the cache, not here, for the licence reason above; one
command each makes them on any machine (`make feynman_qcla_mod_7 --twin
nam_heavy`).

## The optimisation task

For this task the source circuit is the benchmark and the agent's certified
result is the score. `optimization.json` lists every T-bearing circuit of the
catalogue by tier, 96 in all, with `recommended: true` on a ladder of one or
two rungs per family and tier (55 circuits), and under `tools` what
uncertified tools reach on the same gate list: T-count, gates, `CX` count,
seconds, and how the output relates to the source. `best_uncertified_t_count`
is the smallest T-count among outputs that were not found to differ from the
source, so the wrong `qcla_mod_7` output (235) and T-par's differing outputs
do not count; TZAP's twenty `unchecked` outputs count, as PyZX's do. Every
circuit has a `best_uncertified_t_count`.

- `pyzx_teleport` and `pyzx_full_reduce` were run here on every T-bearing
  circuit up to 8000 gates. Our full_reduce numbers reproduce PyZX's
  published T-counts wherever both exist (`adder_8` 173, `mod5_4` 8,
  `gf2^16_mult` 1040, …).
- `nam_light`, `nam_heavy`, `tpar`, `pyzx_published` are the published
  outputs, for the 28 Feynman circuits that have them. They match the
  literature's tables (`adder_8`: 399 to 215 by Nam et al., 173 by PyZX).
- `tzap` was run on all 96, the one tool here that is linear in the gate
  count. On the 74 circuits where another tool's output stands, TZAP's `-O2`
  T-count equals the best of them on 64 and is smaller on the four tier-4
  rungs where only teleportation had run; six times PyZX's `full_reduce`
  (and, where it exists, PyZX's published output) is smaller: `mod5_4` 8
  against 16, `adder_8` 173 against 215, `ham15_med` 212 against 234,
  `csla_mux_3` 62 against 64, `multiplier_n15` 70 against 74,
  `multiplier_n45` 634 against 650. On the 22 circuits past 8000 gates it is
  the only number: `hwb8` 5887 to 3561, `gf2^32_mult` 7168 to 4128,
  `multiplier_n75` 7560 to 1802, `multiplier_n400` 222 320 to 51 202,
  `hwb12` 171 465 to 86 173, `gf2^256_mult` 458 752 to 262 400; the
  synthesised QFTs give up the least (`qft_q050` 557 027 to 405 409).
- The tier-4 circuits under 8000 gates got PyZX too: teleportation finished
  on all five, `full_reduce` on `adder_n118` alone (equal up to `−1`) and was
  stopped at 240 s on the other four.

The recommended ladder (`scripts/circuit_pairs.py optimization --table`; a
starred T-count belongs to an output that differs from its source, an empty
cell means no published output, `—` that the tool was not run at that size):

<!-- BEGIN OPTIMISATION TABLE -->
| Circuit | Tier | Qubits | Gates | T | PyZX teleport | PyZX full_reduce | Nam heavy | T-par | PyZX published | TZAP |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `feynman_tof_3` | 1 | 5 | 57 | 21 | 19 | 15 | 15 | 15 | 15 | 15 |
| `feynman_mod5_4` | 1 | 5 | 79 | 28 | 22 | 8 | 16 | 16 | 8 | 16 |
| `feynman_tof_5` | 1 | 9 | 133 | 49 | 43 | 31 | 31 | 31\* | 31 | 31 |
| `gen_cuccaro_4` | 1 | 10 | 137 | 56 | 48 | 32 |  |  |  | 32 |
| `qasmbench_adder_n10` | 1 | 10 | 142 | 56 | 48 | 32 |  |  |  | 32 |
| `feynman_barenco_tof_4` | 1 | 7 | 146 | 56 | 48 | 28 | 28 | 28 | 28 | 28 |
| `feynman_mod_mult_55` | 1 | 9 | 147 | 49 | 43 | 35 | 35 | 37\* | 35 | 35 |
| `qasmbench_sat_n7` | 1 | 7 | 180 | 70 | 62 | 46 |  |  |  | 46 |
| `feynman_qft_4` | 1 | 5 | 187 | 69 | 67 | 67 |  |  |  | 67 |
| `feynman_vbe_adder_3` | 1 | 10 | 190 | 70 | 56 | 24 | 24 | 24 | 24 | 24 |
| `feynman_csla_mux_3` | 2 | 15 | 210 | 70 | 64 | 62 | 64 | 62\* | 62 | 64 |
| `feynman_rc_adder_6` | 2 | 14 | 244 | 77 | 59 | 47 | 47 | 63\* | 47 | 47 |
| `feynman_gf2_4_mult` | 2 | 12 | 289 | 112 | 96 | 68 | 68 | 68\* | 68 | 68 |
| `feynman_hwb6` | 2 | 7 | 319 | 105 | 95 | 75 |  |  |  | 75 |
| `qasmbench_qram_n20` | 2 | 20 | 321 | 140 | 128 | 96 |  |  |  | 96 |
| `feynman_tof_10` | 2 | 19 | 323 | 119 | 103 | 71 | 71 | 71\* | 71 | 71 |
| `feynman_mod_red_21` | 2 | 11 | 346 | 119 | 107 | 73 | 73 | 73\* | 73 | 73 |
| `qasmbench_adder_n28` | 2 | 28 | 424 | 168 | 144 | 96 |  |  |  | 96 |
| `gen_cuccaro_14` | 2 | 30 | 477 | 196 | 168 | 112 |  |  |  | 112 |
| `feynman_csum_mux_9` | 2 | 30 | 532 | 196 | 168 | 84 | 84 | 112 | 84 | 84 |
| `feynman_ham15_low` | 2 | 17 | 535 | 161 | 147 | 97 |  |  |  | 97 |
| `feynman_qcla_com_7` | 2 | 24 | 559 | 203 | 169 | 95 | 95 | 95\* | 95 | 95 |
| `qasmbench_multiplier_n15` | 2 | 15 | 574 | 252 | 204 | 70 |  |  |  | 74 |
| `feynman_barenco_tof_10` | 2 | 19 | 578 | 224 | 192 | 100 | 100 | 100 | 100 | 100 |
| `qasmbench_sat_n11` | 2 | 11 | 679 | 294 | 254 | 126 |  |  |  | 126 |
| `feynman_gf2_7_mult` | 2 | 21 | 865 | 343 | 301 | 217 | 217 | 217\* | 217 | 217 |
| `feynman_grover_5` | 2 | 9 | 1023 | 336 | 290 | 166 |  |  |  | 166 |
| `feynman_qcla_mod_7` | 2 | 26 | 1120 | 413 | 351 | 237 | 235\* | 249\* | 237 | 237 |
| `feynman_adder_8` | 2 | 24 | 1128 | 399 | 349 | 173 | 215 | 215\* | 173 | 215 |
| `feynman_ham15_med` | 2 | 17 | 1600 | 574 | 504 | 212 |  |  |  | 234 |
| `feynman_gf2_10_mult` | 2 | 30 | 1747 | 700 | 600 | 410 | 410 | 410 | 410 | 410 |
| `feynman_qcla_adder_10` | 3 | 36 | 657 | 238 | 208 | 162 |  |  |  | 162 |
| `qasmbench_adder_n64` | 3 | 64 | 988 | 392 | 336 | 224 |  |  |  | 224 |
| `gen_tof_50` | 3 | 99 | 1455 | 679 | 583 | 391 |  |  |  | 391 |
| `gen_cuccaro_49` | 3 | 100 | 1667 | 686 | 588 | 392 |  |  |  | 392 |
| `gen_barenco_tof_50` | 3 | 99 | 2880 | 1344 | 1152 | 580 |  |  |  | 580 |
| `feynman_gf2_16_mult` | 3 | 48 | 4459 | 1792 | 1536 | 1040 | 1040 | 1040 | 1040 | 1040 |
| `feynman_mod_adder_1024` | 3 | 28 | 5425 | 1995 | 1739 | 1011 | 1011 | 1011 | 1011 | 1011 |
| `qasmbench_multiplier_n45` | 3 | 45 | 5981 | 2646 | 2124 | 634 |  |  |  | 650 |
| `feynman_ham15_high` | 3 | 20 | 6712 | 2457 | 2173 | 1019 |  |  |  | 1019 |
| `qasmbench_multiplier_n75` | 3 | 75 | 17077 | 7560 | — | — |  |  |  | 1802 |
| `feynman_gf2_32_mult` | 3 | 96 | 17658 | 7168 | — | — |  |  |  | 4128 |
| `feynman_hwb8` | 3 | 12 | 18220 | 5887 | — | — |  |  |  | 3561 |
| `qasmbench_adder_n433` | 4 | 433 | 6769 | 2688 | 2304 | — |  |  |  | 1536 |
| `gen_cuccaro_512` | 4 | 1026 | 17409 | 7168 | — | — |  |  |  | 4096 |
| `tzap_cobble_t_laplacian_filter` | 4 | 11 | 34138 | 13442 | — | — |  |  |  | 12842 |
| `feynman_gf2_64_mult` | 4 | 192 | 70075 | 28672 | — | — |  |  |  | 16448 |
| `feynman_hwb10` | 4 | 16 | 91642 | 29939 | — | — |  |  |  | 15921 |
| `feynman_gf2_128_mult` | 4 | 384 | 279419 | 114688 | — | — |  |  |  | 65664 |
| `tzap_qft_qft_q020_d32421` | 4 | 20 | 309835 | 167567 | — | — |  |  |  | 122387 |
| `qasmbench_multiplier_n400` | 4 | 400 | 501877 | 222320 | — | — |  |  |  | 51202 |
| `feynman_hwb12` | 4 | 20 | 514412 | 171465 | — | — |  |  |  | 86173 |
| `tzap_cobble_t_ols_ridge` | 4 | 22 | 587755 | 255692 | — | — |  |  |  | 119052 |
| `tzap_qft_qft_q050_d87171` | 4 | 50 | 1030570 | 557027 | — | — |  |  |  | 405409 |
| `feynman_gf2_256_mult` | 4 | 768 | 1115899 | 458752 | — | — |  |  |  | 262400 |
<!-- END OPTIMISATION TABLE -->

A translated circuit is obtained with `scripts/circuit_sources.py translate
NAME --qasm --out DIR` (the JSON gate list the harnesses read, and the same
circuit as OpenQASM in the alphabet's own gates for TZAP, PyZX or Feynman);
`translated_sha256` in both JSON files says whether two machines hold the
same list. `scripts/optimizer_harness.py import-pair` takes any file under
`pairs/` and keeps its original as the task and its twin as a baseline.

## Reproduce

The virtualenv Python has numpy and pyzx 0.9.0 (`uv venv --python 3.12
~/.circuiteq-harness/envs/pyzx`, then `uv pip install --python
~/.circuiteq-harness/envs/pyzx/bin/python numpy pyzx==0.9.0`); the system
`python3` has neither. TZAP lives in the virtualenv next to it
(`benchmarks/harness/notes/README.md`; `CIRCUITEQ_HARNESS_TZAP` names
another binary, as it does for the harness). Fetching and translating need
no package; the numeric checks need
numpy; the PyZX twins and the PyZX parser cross-check need pyzx.

```bash
PY=~/.circuiteq-harness/envs/pyzx/bin/python
$PY scripts/circuit_sources.py --self-test
$PY scripts/circuit_sources.py fetch                  # tiers 1 to 3: 2.5 MB, 15 s
$PY scripts/circuit_sources.py fetch --all            # tier 4 and the published outputs: 85 MB
$PY scripts/circuit_sources.py translate feynman_tof_5 gen_cuccaro_64 --qasm --out /tmp/circuits
$PY scripts/circuit_sources.py catalogue --write      # recompute manifest.json, about 15 minutes
$PY scripts/circuit_sources.py catalogue --table      # the tier tables above; --readme puts them here

$PY scripts/circuit_pairs.py --self-test
$PY scripts/circuit_pairs.py batch                    # the first batch; resumes; 8 minutes a call
$PY scripts/circuit_pairs.py batch --tcounts          # PyZX and TZAP on every other T-bearing circuit
$PY scripts/circuit_pairs.py batch --tcounts --twin tzap --minutes 30   # TZAP alone, tier 4 included
$PY scripts/circuit_pairs.py make gen_cuccaro_64 --twin peephole tzap --out /tmp/pairs
$PY scripts/circuit_pairs.py optimization             # optimization.json, from pairs/index.json
$PY scripts/circuit_pairs.py optimization --readme    # its recommended ladder, into this file
$PY scripts/circuit_pairs.py table                    # the pairs table above; --write puts it in pairs/README.md

python3 scripts/agent_harness.py import-pair benchmarks/circuits/pairs/feynman_tof_5__pyzx_teleport.json
```

`gen_<family>_<size>` works for any size (`gen_tof_200`, `gen_surface_11`),
which is how a held-out ladder is drawn: pick sizes that are not listed here.
