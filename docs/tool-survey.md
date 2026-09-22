# Equivalence checkers and optimizers: where each stops scaling

A literature survey for CircuitEq, 22 September 2026. It answers two questions:
at what circuit size and structure does each published equivalence checker and
optimiser become impractical, and which metrics do the papers use for the
complexity of a circuit and the difficulty of proving two circuits equal.

**How it was built.** About 150 primary sources were read: papers (full text
where it was accessible), repositories and tool documentation. Independent
readers then went back to the sources and re-checked the 89 numbers the tables
depend on: 71 held as stated and 18 needed a correction, none of them to a
headline claim. The corrected values are the ones used here, and section 8
lists the corrections. TZAP had its own search, a full read of both papers and
the repository, and two separate fact-checks. Numbers are from each paper's
own evaluation, on its hardware and time limits, which differ between papers;
treat the ceilings as orders of magnitude, not as comparable benchmarks. The
equivalence notion is "equal up to global phase" unless a row says otherwise.
Bracketed numbers are the references at the end.

## Summary

- **Qubit and gate counts are poor predictors of difficulty.** Each technique
  has one structural quantity that sets its cost: path variables (roughly the
  number of Hadamards) for path sums; non-Clifford phases that survive
  simplification for the ZX-calculus; the number of distinct amplitudes, and
  whether the two circuits' gate orders line up, for decision diagrams;
  treewidth for tensor networks; window width for synthesis and rule-based
  rewriting. Feynman verifies a 197-qubit Toffoli in 5.6 s and runs out of
  memory on the 12-qubit `hwb8`, which has 2,282 path variables [21].
- **The hard case for a checker is two equivalent circuits that look very
  different.** Non-equivalence is usually found in one to three random
  simulations, but not always: a 23-qubit QFT with one gate removed took
  decision diagrams over an hour, against 2 s when the pair was equal [5].
- **The optimisers that scale linearly all bound the region they optimise at
  once:** Nam et al.'s Light mode, OAC/POPQC and TZAP. Global search (Quartz,
  Queso, e-graphs, GUOQ) stops paying off around 10⁴ to 10⁵ gates.
- **Checking lags optimising by orders of magnitude.** TZAP optimises 11
  million gates in seconds; its own tests run QCEC only on the 23 smallest
  Feynman-suite files, because QCEC "effectively hangs" from `gf2^8_mult` (24
  qubits, 1,139 gates) upward [53].
- **Floating-point checkers can be wrong, and exact ones restrict the gate
  set.** QCEC and TDD have published wrong verdicts (section 1); SliQEC,
  AutoQ and Feynman avoid rounding by accepting only a fixed gate set.

## 1. Equivalence checkers

| Checker (method) | What it decides | Where it stops (each paper's evaluation) | What makes it fail |
|---|---|---|---|
| Dense unitary (Qiskit `Operator.equiv`) | Exact up to tolerance | 16·4ⁿ bytes: about 14 to 15 qubits (15-qubit `rd84_142` ran out of 8 GB) [10] | n |
| QCEC, decision diagrams (alternating and construction schemes) [1, 2, 4, 7] | Complete; floating-point edge weights | Easy: reversible and oracle-heavy circuits (`bw_291`, 87 qubits, 19 s; Grover-11, 308k gates, 0.07 s). Hard: Qiskit-compiled RevLib circuits (22 to 34 qubits, 13.5k gates) exceed 1 h under every generic strategy; with knowledge of the compilation flow the same circuits take 0.03 to 2.6 s, and 134k gates take 9.5 s [7]. QFT-38 (10.4k gates) exceeds 1 h; QPE grows 2 to 3× per qubit, 173 s at 50 qubits. Exact Clifford+T DDs are bounded by 2^t·poly [24] | Gate orders that do not line up; many distinct angles (QFT, QPE, W-state), which stop DD nodes being shared. Wrong verdicts from rounding: missed phase shifts of 1e-7 [25]; mishandled angles at or below π/2²⁷, and in hybrid mode all 169 unitary-versus-dynamic pairs failed, 27 with a wrong verdict [23] |
| QCEC, random-stimulus simulation [3] | Refutes only | Typical compilation bugs are found in 1 to 3 simulations. One removed gate is detected 80 to 97% of the time with 16 stimuli (85.2% on average) [1]; computational-basis stimuli catch one *added* gate 54.9% of the time; random Clifford states reach 99% at about 50 s per instance | 2ⁿ per simulation on dense states; faults in multi-controlled gates touch few columns; a diagonal difference is invisible to basis stimuli (section 7) |
| ZX-calculus (PyZX `verify_equality` [13], QCEC's ZX checker [5]) | Polynomial; complete for Clifford circuits; otherwise "inconclusive", and it cannot refute | QFT-75 in 1.23 s where DDs exceed 1 h; fails on Random-Walk-9 (29k to 42k gates, over 1 h), Grover-11 (2,178 s) and the RevLib circuits of 95k to 173k gates (over 1 h) [5] | Non-Clifford phase gadgets that survive simplification; incomplete even for equivalent reversible circuits with one ancilla [5, Thm. 2] |
| QCEC, parameterised circuits [6] | Complete if phases are linear in the parameters | 127 qubits, 3,965 parameters, 446k gates; slowest 1,904 s. Refutation by random instantiation times out at 20 to 50 qubits | Non-linear dependence on the parameters |
| Stabiliser decomposition (quizx, PyZX) [15–17] | Complete | Cost about 2^{αt}, α ≈ 0.40 to 0.47. On 50-qubit random circuits in 5 min: every circuit with T ≤ 30, 88% at T = 40, 4% at T = 50; sparser 100-qubit circuits: 44% at T = 60 | t, the non-Clifford count left after simplification |
| Feynman, `feynver` (path sums) [21] | Polynomial and complete for Clifford circuits; incomplete for Clifford+T (unique normal forms would give P = coNP) | GF(2³²) multiplier (96 qubits, 252 path variables, 25.5k gates) in 431 s; out of memory at 6 GB on GF(2⁶⁴) (508 path variables), `cycle17_3` (1,366) and `hwb8` (12 qubits, 2,282); QFT stops at 31 qubits (integer overflow) | Path variables, the Hadamards no rule eliminates, and the degree of the phase polynomial; no arbitrary rotations |
| QuPRS (path sums plus weighted model counting) [22] | Complete up to global phase | 29 of 35 instances at 200 s (the paper's table has 36 rows, of which 30 solved); times out on Grover-6 (1,568 gates), QFT-24 and QPE-24 | Reduction rules fire on about half of the Grover, QAOA and VQE instances; the rest goes to model counting, which is #P |
| Quokka# / ECMC (Pauli basis plus model counting) [25] | Complete; 2n model-counting calls | 64-qubit W-state (1,135 gates) in 70 s where QCEC timed out; Grover-5 (499 gates) and QPE-16 exceed 300 s. Refutation is cheap: it stops at the first failing call | T and rotation gates split each Pauli term |
| Clifford tableau (CCEC with Stim [26]; QuaSARQ on a GPU [27]) | Decision procedure, O(n·m) | CCEC: 1,000 qubits at depth 10,000 (5 to 10 million gates) in about 22 s. QuaSARQ: 500k qubits and 34M gates on a 24 GB GPU | Clifford circuits only; memory Θ(n²) |
| SliQEC (exact, bit-sliced BDDs) [8, 9] | Exact | Random 100-qubit pairs (400 against about 1,230 gates) in 58 s and 79 MB; partial equivalence: 13 of 20 instances time out at 20 data qubits | No arbitrary rotations, so it is left out of most rotation-heavy benchmarks |
| TDD / LimTDD [10–12] | Canonical tensor DDs; floating point | TDD needs 525k nodes for `qft_10` and 8.4M for `qft_12` (LimTDD: 21 and 25); noisy approximate equivalence tested only to 16 qubits | QuPRS left it out because rounding made its results wrong [22] |
| AutoQ / LSTA (tree automata) [18, 19] | Exact, for Hoare-style pre- and postconditions | Grover on 40 qubits (141k gates) in 1 min 8 s; `add64` (193 qubits) against its Qiskit-optimised version in 24 s | Exponentially many distinct amplitudes (QFT); angles must be multiples of π/4 |
| MPO, tensor networks, FeynmanDD [28–30] | Approximate (SVD threshold) or exact counting | Polynomial when there are few long-range gates; every method nears exponential cost under all-to-all entangling layers (tested up to 32 × 32) | Treewidth, linear rank-width, bond dimension |
| Constant depth (Yu, Trinh, Reps) [31] | Decision procedure, f(d)·O(n) | 100 qubits at depth 3 in 4.5 to 32 s; at 30 qubits, depth 8 took 11.8 h | Light-cone size, exponential in depth |
| Proof assistants (SQIR/VOQC [33], CoqQ, Qbricks, Giallar [34]) | Verified | VOQC's optimiser is about 7.2k lines of Coq; the verified Shor about 14k; Giallar verified 44 of 56 Qiskit passes | Proof effort, and restriction to fragments. No scalable Lean *checker* was found besides CircuitEq |

The QCEC figures are from the papers of the version they describe; the tool's
current default (3.10.0) runs the alternating DD, simulation and ZX checkers in
parallel with no timeout [4]. Approximate checking by the projective
Hilbert–Schmidt distance was merged on 6 September 2026 (PR #443). Symbolic
simulation with weighted CFLOBDDs, which is not a two-circuit checker, reaches
GHZ on 2 million qubits but Grover on only 16 [20].

## 2. Optimisers

### 2.1 Rewriting, pass-based and search-based

| Optimiser | Where it becomes impractical | Why |
|---|---|---|
| Qiskit (levels 1 to 3) | Benchpress: all 1,032 tests, up to 930 qubits and about 10⁶ two-qubit gates, in 0.18 days [45]. Level 3 timed out on 12 of 135 circuits in TZAP's 3-hour suite [52] | Superlinear passes at level 3 |
| TKET, BQSKit | Fail 8% (TKET) and 19% (BQSKit) of the Benchpress tests, mostly timeouts; their day totals were estimated, not measured [45] | Resynthesis passes |
| Nam et al. [35] | Light: a 2,048-qubit adder (382k gates) in 0.2 s, GF(2¹⁶³) (399k gates) in 1.4 h. Heavy: 6.6 h at 188k gates | Routines of O(g²) to O(g³) in the gate count g |
| VOQC (Coq-verified) [33] | Worst case about 10⁴× slower than Nam (GF(2¹⁶³): 7.7 h); timed out on 30 of 135 at 3 h [52]; did not finish six circuits of 0.7M to 5.5M gates in 12 h [40] | Searching pairs of rotations is quadratic |
| OAC / POPQC [40, 41] | 5.3k to 5.5M gates; Shor-16 in 649 s against 70,475 s for VOQC | Segments of Ω = 40 layers, so optimisations across segment boundaries are missed |
| Quartz [36] | Rules with 7 gates on 3 qubits number 379,864 and take 2.9 h to generate; a 4-qubit set does not fit in 512 GB. 24 h per circuit, on circuits of at most 1,347 gates in the Nam and IBM gate sets (about 10× larger in the Rigetti set). At most 10% on 10⁵ to 10⁶-gate circuits in 12 h [40] | Rule sets grow about 7× per extra gate |
| Queso [37] | Rules limited to 3 qubits, and to size 6 on the Nam gate set (14,544 rules in 135 s); only 35 of 701 IBM rules were ever used | Candidate space up to 10¹⁸; correctness is probabilistic (polynomial identity testing) |
| Quarl [38] | 6 h per circuit plus a GPU; 35.2% total reduction against 31.0% for Queso | Partitioning misses optimisations that cross partitions |
| GUOQ / Wisq [39] | 1 h, up to 36 qubits; best two-qubit results at that scale (28% on IBM hardware). With resynthesis turned off, TZAP's 3-hour runs saw essentially no reduction above 10k gates [52] | Resynthesis limited to 3 qubits; random search |
| Quasar (e-graphs) [42], Qsymb [43] | Quasar's own suite (median 232 gates) takes 12.2 h in total, and it ran out of 64 GB on 95 of TZAP's 135 circuits [52]. Qsymb: up to 17k gates in 60 min | E-graphs grow in memory |
| PyZX `full_reduce` [14, 13], QuiZX [17] | PyZX timed out at 1 h on `gf2^64_mult` (70k gates) [51]; QuiZX timed out on 26 of 135 and its extraction crashed on 3 of 6 Cobble circuits [51, 52]. In this repository's catalogue `full_reduce` was stopped at 240 s on four tier-4 circuits below 8k gates | Extraction is #P-hard in general and inflates the CNOT count [32] |
| Feynman `feynopt` [21] | 30.7 min on `gf2^64_mult`; timed out on 52 of 135 [51, 52] | Symbolic parities grow heavier as H and CX interleave more densely |
| T-par [48] | 26.5 h on GF(2⁶⁴) | O(g³) |
| TODD, FastTODD, TOHPE [49, 50] | TODD took 11.4 h on `adder_8` (24 qubits plus 71 ancillas); FastTODD and TOHPE hit the 24 h cap on the 640-qubit DEFAULT cipher; exact Reed–Muller decoding stops at n ≤ 6 | One ancilla per Hadamard gadget, so n + h qubits |
| AlphaTensor-Quantum [44] | Circuits over 60 qubits (after gadgets) must be split; optimality confirmed with Z3 only up to 20 T gates | The action space is 2ᴺ |
| TZAP [51–53] | No breaking point reported (section 3) | Limits are on optimisation power, not scale |

### 2.2 Synthesis and exact methods (exponential in the block's qubit count)

| Method | Practical limit |
|---|---|
| QSearch, LEAP, QFAST [54–56] | 4, 6 and 7 qubits. The 4-qubit QFT took 114 h in QSearch's first version (40 min later); some 6-qubit LEAP and 7-qubit QFAST runs exceed 12 h |
| QFactor [57] | Instantiation reaches 12 qubits, with about 15% success |
| Partition plus resynthesis (QGo, TopAS, GUOQ) [58, 59, 39] | Blocks of 3 to 4 qubits; with 4-qubit blocks QGo compiles a 60-qubit circuit in hours |
| Synthetiq [60] | 2 to 4 qubits plus at most one ancilla, T-count up to 11, up to 8 h |
| SAT-optimal Clifford synthesis [61, 62] | 5 to 6 qubits and about 15 to 20 gates (the paper's v2 corrected its claim from 27 qubits to 6); depth-optimal: 5 qubits in 3 h |
| Clifford and CNOT databases [63, 64] | Optimal 6-qubit Cliffords need 2.1 TB (about six months to build); every optimal 7-qubit CNOT circuit took 8,483 s on 128 cores, and 8 qubits was out of reach even with 1.5 TB |
| Exact T-count and T-depth [65, 66] | 2 to 4 qubits |
| Layout synthesis [67, 68] | SATMap's largest solved circuit has 598 two-qubit gates; neutral-atom optimal compilation reaches 22 qubits; lattice-surgery SAT (LaSsynth) Bernstein–Vazirani at 30 qubits and random Cliffords at 6 [70] |

## 3. TZAP

**Identity.** github.com/qqq-wisc/tzap, by Aws Albarghouthi (UW–Madison), is
described in two preprints: *Linear-Time T-Gate Optimization via Random
Abstraction* (P1, arXiv 2605.13929, v2 of 10 July 2026) [51] and *Fast
Quantum-Circuit Superoptimization* (P2, IACR ePrint 2026/2115, approved
22 September 2026) [52]. It ships as PyPI `tzap`, crates.io `tzap-opt` and a
Homebrew tap, with Qiskit and PennyLane integrations. It is an optimiser, not
a checker.

**Method.** At `-O2` and `-O3` each round runs CnotMin, CancelGates, SuperOpt
and PhaseFoldRand; `-O1` is CancelGates and PhaseFoldRand only.

- *PhaseFoldRand* (P1) gives every wire a random 128-bit parity tag: CX XORs
  tags, H draws a fresh one, X complements, and rotations whose tags match
  are merged through a hash map. The probability of an unsound merge is at
  most C(m,2)·2⁻¹²⁸, and the expected cost is O(n + m). It finds every merge
  the exact affine-parity analysis finds (P1, Lemma 4.2), and nothing that
  needs reasoning through a Hadamard.
- *SuperOpt* (P2) scans windows of at most 3 qubits and 25 gates against a
  table (a "murm") of 200,000 minimal circuits per qubit count, built by
  breadth-first enumeration over the exact ring ℤ[1/√2, i] and canonicalised
  up to global phase. Every fingerprint hit is re-checked exactly, so a
  collision can only lose a rewrite. The scan is greedy and runs to a
  fixpoint.
- *CnotMin* (repository only) resynthesises CNOT-dihedral blocks from their
  linear map and phase polynomial, a port of Feynman's `-cnotmin`; it keeps a
  block only if it is strictly better.

**Scale: no breaking point reported.** Phase folding alone: 148M gates in
under a minute and about 500M in about 2 minutes. The full pipeline finished
all 135 circuits of P2's suite (1k to 11M gates, median 18k) with a median
runtime of 0.08 s. On `gf2^64_mult` (70,075 gates): TZAP 17.9 ms, VOQC 5.3 min,
QuiZX 17.7 min, Feynman 30.7 min, PyZX over 1 h. On `gf2^128_mult`, `hwb12`
and `gf2^256_mult` every competitor fails while TZAP takes 0.06 to 0.25 s.

**Limits, on optimisation power.** Hadamards are fresh variables and `ccx` is
opaque to phase folding; windows are at most 3 qubits and the table is
incomplete; windows whose exact coefficients overflow the table's integer
width are skipped; Feynman leads on rotation count by 1.5 percentage points at
the median. In this repository's catalogue TZAP matched the best T-count on 64
of 74 circuits, and PyZX `full_reduce` did better on 6 (`mod5_4` 8 against 16,
`adder_8` 173 against 215, `ham15_med` 212 against 234, `csla_mux_3`,
`multiplier_n15`, `multiplier_n45`).

**How correctness is assured.** The Rust binary gives no certificate. A
separate Lean 4 port (34 files, no `sorry`) proves each deterministic pass
correct and bounds PhaseFoldRand's failure probability, but it is not the
benchmarked binary, and the Lean proof of the table's minimality was deleted
in PR #11 (5 September 2026). The Rust tags come from a SipHash-based
generator, not the independent uniform draws the bound assumes. Validation is
matrix comparison up to 6 qubits, Feynman's path-sum verifier on most feasible
Feynman-suite circuits, and QCEC on the smallest files only.

**Skeleton.** Measured on TZAP 0.6.1 with a network of five `ccx` gates:
`-O1` kept the 30 CNOTs of the five Toffoli decompositions, `-O2` and `-O3`
rewrote them (25 CNOTs). The catalogue finds that `-O2` output keeps the
CX/H/X skeleton on 18 of its 99 pairs (`CLAUDE.md`).

**Metrics.** T-count (rotation count), total and two-qubit gate counts,
runtime; P1 explains the competitors' slowdown by *parity weight* and
*Hadamard density*.

## 4. What measures difficulty

### 4.1 The quantity that sets each technique's cost

| Technique | Governing quantity |
|---|---|
| Dense unitary or state vector | n (4ⁿ or 2ⁿ) |
| Decision diagrams | Peak node count (about 4×10⁵ in QCEC's tables); number of distinct amplitudes; whether the gate orders line up (Qiskit level, mapping); entanglement pattern (2D cluster states already need exponential QMDDs [11]) |
| ZX-calculus | Non-Clifford spiders left after simplification; ancillas |
| Stabiliser decomposition | T-count after simplification, cost 2^{αt} |
| Path sums | Path variables (about the number of H gates); degree and term count of the phase polynomial; how often the rules apply |
| Pauli basis, model counting | T-count: 2^{min(t, 2n)} [46]; T-depth: NP-hard already at O(log n) [46] |
| Tensor networks, MPO | Treewidth, linear rank-width, bond dimension, long-range gates |
| Parameterised circuits | Number of parameters k; linearity; the cutoff (2b+1)^k [47] |
| Random stimuli | Detection probability, number of stimuli, measurements m (2^m branches) |
| Rewrite-rule optimisers | Rule-set size (gates, qubits); number of equivalence classes; candidate space; search budget; parity weight and Hadamard density [51] |
| Synthesis | Block width k (4^k); depth and parameters (3n + 6d); target T-count; Hadamard gadgets (n + h) |

### 4.2 What papers report

- **Size:** qubits, total gates, depth, and counts per gate type (CX or
  two-qubit, T or Rz, H).
- **Quality:** percent reduction (geometric mean), percentage-point margins,
  win/tie/loss counts, estimated fidelity, Nam et al.'s cost
  #T + 0.01·log n·#CX.
- **Tool cost:** runtime within a fixed budget (200 s to 24 h) and memory.
- **Benchmark features:** SupermarQ's program communication, critical depth,
  entanglement ratio, parallelism, liveness and measurement density;
  QASMBench's gate density.

### 4.3 Complexity-theoretic limits

- **Checking.** Approximate identity check is QMA-complete [71], even at
  constant depth [72]. Exact non-identity is NQP-complete [73]. Equivalence of
  reversible (classical) circuits is coNP-complete. Clifford equivalence is in
  P. Exact Clifford+T equivalence is fixed-parameter tractable in the T-count;
  it is in P at T-depth 2 and NP-hard at T-depth O(log n) [46].
- **Optimising.** Minimising T-count, T-depth, CNOT count or H count is
  NP-hard [74]; exact optimisation is co-NQP-hard [75]; minimum CNOT synthesis
  is claimed NP-complete in a preprint of 3 September 2026 [76]; ZX circuit
  extraction is #P-hard [32].
- **Lower-bound tools.** Stabiliser nullity is at most 2n, so it can prove
  T-count lower bounds for small gadgets, never for large optimiser outputs
  [77]. Complexity-growth theorems say random circuits are incompressible, so
  "no reduction" on random benchmarks is expected [78].

## 5. Neighbouring tool families

- **Lattice surgery and Pauli-based computation.** Exact SAT layout works on
  small Clifford blocks only; heuristics (liblsqecc, DASCOT, PureMagic) reach
  10² to 10³ qubits and about 10⁸ instructions [69, 70]. None checks the
  equivalence of its output at scale.
- **Pauli-string Hamiltonian-simulation compilers** (Paulihedral, Tetris,
  Rustiq, QuCLEAR, Symphony): O(n³m²) in the worst case; Rustiq took
  14,802 s on UCC-(10,20). Several preserve only measurement outcomes,
  equality up to a final Clifford, or Trotter-level approximation [79].
- **Photonic and neutral-atom compilers:** OnePerc needs 192 GB for 64
  qubits; OLSQ-DPQA is optimal to 22 qubits [68].
- **Hybrid quantum-classical checkers:** hybrid path sums verified QFT
  equivalence at 500 qubits in 132 s [23].

## 6. Where CircuitEq sits

From `benchmarks/scale/README.md`:

| Checker | Measured cost |
|---|---|
| Tableau (`Tableau.lean`) | `2n · gates` steps, about 0.2 to 0.3 ms per generator and gate |
| Phase polynomial (`PhasePoly.lean`) | Linear in gates: 10,200 gates on 300 wires in 10.1 s of kernel time at 5.26 GB; what grows is the `C(n,3)`-bit triple plane |
| Basis decide | `gates · 4ⁿ` steps of about 150 µs and 40 KB; the seven-qubit Steane pair in 78 s at 1.98 GB when chunked; eight qubits take minutes, ten over an hour |

The hardest axis for exact symbolic checkers is path variables. That is
`QUEUE.md`'s phase polynomials with Hadamard variables, which Feynman handles
only incompletely.

## 7. A pair past every checker

`scripts/hard_pair.py` builds a pair designed to push every family of checker
past its limit at once: an exact Clifford+T circuit A of random all-to-all
rounds, and the same unitary B recompiled into rotations about dense Pauli
strings, with spider nests folded in (15 T-type rotations about the products
of 4 commuting Paulis, whose product is the identity; no ZX rule removes
them). Two mutants, each one gate away from B, are not equivalent. The
construction, why each family should fail, and the measured ladder from 8 to
64 qubits are in `benchmarks/hard_pair/README.md`.

"Past every published checker" is not intrinsic hardness. B is built by a
derivation, so a checker that computed each circuit's rotation form with
tableaux, normalised the rotation order modulo commutation and compared
commuting layers by phase-polynomial normal forms would decide this family in
polynomial time. None exists; in this library's terms the pieces are
`Tableau.lean`, `PhasePoly.lean` in a rotated frame, and a frame-change step
in `Certificate.lean`.

## 8. Corrections found in verification, and what stays unverified

Corrections applied above:

- QCEC's ZX paper: the RevLib gate range is 12k to 173k, not 12k to 23k; the
  ZX checker only failed to verify Nam et al.'s `qcla_mod_7`, and Feynman
  showed it incorrect.
- QuPRS: the largest instance has 1,568 gates; the prose counts 35 instances
  and the table 36.
- CCEC's 1,000-qubit result is at depth 10,000, not 10,000 gates.
- SliQEC's partial equivalence: 13 of 20 time out at 20 data qubits (one
  algorithm), not "every instance from 20 qubits".
- Quarl's published figures are 35.2% against Queso's 31.0% (the preprint had
  35.8% against Quartz's 28.3%).
- OAC: Queso ran out of memory or failed to parse on some circuits, and Quartz
  reached up to 9.6% on some large ones.
- Qsymb's win rates are against GUOQ's rewrite engine alone.
- Benchpress's TKET and BQSKit day totals are estimates.
- GUOQ/Wisq ran in TZAP's evaluation with resynthesis turned off.
- QSearch's 410,250 s is from its first preprint (IWQC 2019).
- QFAST: only two 7-qubit all-to-all runs timed out.
- QFactor: 12 qubits is the tested ceiling, at about 15% success, on CPU as
  well as GPU.
- QGo: the minutes and hours are whole-circuit compile times.
- Optimal CNOT circuits: the 1.5 TB machine was used for the 8-qubit attempt.
- TODD on GF(2¹⁶): its table shows a dash; the partial variant finished
  (76,312 s).
- FastTODD/TOHPE: the run that exceeded 8 TB was PHAGE.
- SAT Clifford synthesis: the paper's v2 lowers its claim from 27 qubits to 6.
- The QCEC bug found by AutoQ's study was in the ZX checker, fixed in 2.1.1.

Not verified: SliQEC's own DAC 2022 results table (paywalled), QuaSARQ's
TACAS paper (bot checks blocked the PDF), Quasar's full text (publisher
403). Several sources are 2026 preprints not yet peer-reviewed: TZAP's P2,
Li and Guan's NP-hardness of CNOT synthesis, Qsymb and SpiderLS.

## References

1. Burgholzer, Wille. Advanced equivalence checking for quantum circuits. IEEE TCAD 40(9), 2021. arXiv:2004.08420
2. Burgholzer, Wille. Improved DD-based equivalence checking of quantum circuits. ASP-DAC 2020. https://www.cda.cit.tum.de/files/eda/2020_aspdac_improved_dd_equivalence_checking_of_quantum_circuits.pdf
3. Burgholzer, Kueng, Wille. Random stimuli generation for the verification of quantum circuits. ASP-DAC 2021. arXiv:2011.07288
4. MQT QCEC. https://github.com/munich-quantum-toolkit/qcec (v3.10.0; PR #443). Burgholzer, Wille, Handling non-unitaries in quantum circuit equivalence checking, DAC 2022, arXiv:2106.01099
5. Peham, Burgholzer, Wille. Equivalence checking of quantum circuits with the ZX-calculus. IEEE JETCAS 2022. arXiv:2208.12820
6. Peham, Burgholzer, Wille. Equivalence checking of parameterized quantum circuits. ASP-DAC 2023. arXiv:2210.12166
7. Burgholzer, Raymond, Wille. Verifying results of the IBM Qiskit quantum circuit compilation flow. QCE 2020. arXiv:2009.02376
8. Wei, Tsai, Jhang, Jiang. Accurate BDD-based unitary operator manipulation for scalable and robust quantum circuit verification. DAC 2022. doi:10.1145/3489517.3530481
9. Chen, Jiang, Hsieh. Partial equivalence checking of quantum circuits. QCE 2022. arXiv:2208.07564
10. Hong et al. A tensor network based decision diagram for representation of quantum circuits. TODAES 2022. arXiv:2009.02618; LimTDD, arXiv:2504.01168
11. Vinkhuijzen et al. LIMDD. Quantum 7, 1108 (2023). arXiv:2108.00931
12. Hong, Ying, Feng, Zhou, Li. Approximate equivalence checking of noisy quantum circuits. DAC 2021. arXiv:2103.11595
13. Kissinger, van de Wetering. PyZX: large scale automated diagrammatic reasoning. QPL 2019. arXiv:1904.04735
14. Duncan, Kissinger, Perdrix, van de Wetering. Graph-theoretic simplification of quantum circuits with the ZX-calculus. Quantum 4, 279 (2020). arXiv:1902.03178; Kissinger, van de Wetering, Reducing T-count with the ZX-calculus, PRA 2020, arXiv:1903.10477
15. Kissinger, van de Wetering. Simulating quantum circuits with ZX-calculus reduced stabiliser decompositions. QST 7, 044001 (2022). arXiv:2109.01076
16. Qassim, Pashayan, Gosset. Improved upper bounds on the stabilizer rank of magic states. Quantum 5, 606 (2021). arXiv:2106.07740
17. quizx. https://github.com/zxcalc/quizx
18. Chen et al. An automata-based framework for verification and bug hunting in quantum circuits. PLDI 2023. arXiv:2301.07747
19. Abdulla et al. Verifying quantum circuits with level-synchronized tree automata. POPL 2025. arXiv:2410.18540
20. Sistla, Chaudhuri, Reps. Weighted context-free-language ordered binary decision diagrams. OOPSLA 2024. arXiv:2305.13610
21. Amy. Towards large-scale functional verification of universal quantum circuits. QPL 2018. arXiv:1805.06908; https://github.com/meamy/feynman
22. Huang, Chareton, Chen et al. QuPRS. TACAS 2026. arXiv:2604.24504
23. Ricciardi et al. SQbricks. arXiv:2511.22523; Chareton et al., hybrid path sums, arXiv:2604.24578
24. Quist, Coopmans, Laarman. Exact decision diagrams for Clifford+T circuits. arXiv:2602.17775
25. Mei, Coopmans, Bonsangue, Laarman. Equivalence checking of quantum circuits by model counting. IJCAR 2024. arXiv:2403.18813
26. Thanos, Coopmans, Laarman. Fast equivalence checking of quantum circuits of Clifford gates. ATVA 2023. arXiv:2308.01206
27. Osama, Thanos, Laarman. QuaSARQ. TACAS 2025. doi:10.1007/978-3-031-90660-2_6
28. Sander, Burgholzer, Wille. Equivalence checking with matrix product operators. Phys. Rev. Research 2025. arXiv:2410.10946
29. Wang, Cheng, Yuan, Ji. FeynmanDD. arXiv:2509.08276
30. Cheng et al. Linear rank-width and path-sum counting. arXiv:2510.06775; Markov, Shi, SICOMP 2008, arXiv:quant-ph/0511069
31. Yu, Trinh, Reps. Equivalence checking of constant-depth circuits. arXiv:2504.01558
32. de Beaudrap, Kissinger, van de Wetering. Circuit extraction for ZX-diagrams can be #P-hard. ICALP 2022. arXiv:2202.09194
33. Hietala, Rand, Hung, Wu, Hicks. A verified optimizer for quantum circuits. POPL 2021. arXiv:1912.02250
34. Tao et al. Giallar. PLDI 2022. arXiv:2205.00661
35. Nam, Ross, Su, Childs, Maslov. Automated optimization of large quantum circuits with continuous parameters. npj QI 4, 23 (2018). arXiv:1710.07345
36. Xu et al. Quartz: superoptimization of quantum circuits. PLDI 2022. arXiv:2204.09033
37. Xu, Molavi, Pick, Tannu, Albarghouthi. Synthesizing quantum-circuit optimizers. PLDI 2023. arXiv:2211.09691
38. Li et al. Quarl: a learning-based quantum circuit optimizer. OOPSLA 2024. arXiv:2307.10120
39. Xu, Molavi, Tannu, Albarghouthi. Optimizing quantum circuits, fast and slow. ASPLOS 2025. arXiv:2411.04104
40. Arora, Xu, Westrick, Liu, Li, Ding, Acar. OAC. IEEE QCE 2025. arXiv:2502.19526
41. Liu, Arora, Xu, Acar. POPQC. SPAA 2025. arXiv:2506.13720
42. Yang, Raun, Tao, Gu. Quasar. PLDI 2026. doi:10.1145/3808254
43. Qiang, Gu. Qsymb. OOPSLA 2026. arXiv:2609.01762
44. Ruiz et al. Quantum circuit optimization with AlphaTensor. Nature Machine Intelligence 7, 374 (2025). arXiv:2402.14396
45. Nation et al. Benchpress. Nature Computational Science 2025. arXiv:2409.08844
46. Nevin. Pauli propagation and the complexity of identity checking. arXiv:2511.17856
47. Ross, Wesley. Parameterized equivalence of quantum circuits. MFCS 2025. arXiv:2506.20985
48. Amy, Maslov, Mosca. Polynomial-time T-depth optimization (T-par). IEEE TCAD 2014. arXiv:1303.2042
49. Heyfron, Campbell. An efficient quantum compiler that reduces T count (TODD). arXiv:1712.01557
50. Vandaele. Lower T-count with faster algorithms (FastTODD, TOHPE). Quantum 9, 1860 (2025). arXiv:2407.08695
51. Albarghouthi. Linear-time T-gate optimization via random abstraction. arXiv:2605.13929
52. Albarghouthi. Fast quantum-circuit superoptimization. IACR ePrint 2026/2115. https://eprint.iacr.org/2026/2115
53. tzap. https://github.com/qqq-wisc/tzap
54. Davis et al. QSearch. arXiv:1912.02727
55. Smith et al. LEAP. arXiv:2106.11246
56. Younis, Sen, Yelick, Iancu. QFAST. IEEE QCE 2021. arXiv:2103.07093
57. Kukliansky, Younis, Cincio, Iancu. QFactor. IEEE QCE 2023. arXiv:2306.08152
58. Wu, Davis, Chong, Iancu. QGo. arXiv:2012.09835
59. Weiden et al. TopAS. arXiv:2206.13645
60. Paradis, Dekoninck, Bichsel, Vechev. Synthetiq. OOPSLA 2024. doi:10.1145/3649813
61. Schneider, Burgholzer, Wille. A SAT encoding for optimal Clifford circuit synthesis. ASP-DAC 2023. arXiv:2208.11713 (v2 correction)
62. Peham, Brandl, Kueng, Wille, Burgholzer. Depth-optimal synthesis of Clifford circuits with SAT solvers. arXiv:2305.01674; Shaik, van de Pol, Q-Synth, arXiv:2504.00634
63. Bravyi, Latone, Maslov. 6-qubit optimal Clifford circuits. npj QI 2022. arXiv:2012.06074
64. Christensen, Jørgensen, Pavlogiannis, van de Pol. Optimal CNOT circuits on 7 qubits. arXiv:2503.01467
65. Gosset, Kliuchnikov, Mosca, Russo. An algorithm for the T-count. arXiv:1308.4134; Mosca, Mukhopadhyay, arXiv:2006.12440
66. Amy, Maslov, Mosca, Roetteler. A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits. arXiv:1206.0758
67. Molavi et al. SATMap. arXiv:2208.13679; Shaik, van de Pol, Q-Synth v2, arXiv:2403.11598; Tan, Cong, OLSQ, arXiv:2007.15671
68. OLSQ-DPQA, Quantum 8, 1281 (2024); OnePerc, ASPLOS 2024, arXiv:2403.01829
69. Leblond, Bennink. Pauli-based computation or direct Clifford+T. Quantum 10, 2187. arXiv:2506.08182; DASCOT, OOPSLA 2025, arXiv:2311.18042; PureMagic, arXiv:2512.06484; liblsqecc, arXiv:2302.02459
70. LaSsynth, ISCA 2024, arXiv:2404.18369; TopoLS, arXiv:2601.23109; SpiderLS, arXiv:2608.30228
71. Janzing, Wocjan, Beth. Non-identity check is QMA-complete. IJQI 2005. arXiv:quant-ph/0305050
72. Ji, Wu. Non-identity check remains QMA-complete for short circuits. arXiv:0906.5416
73. Tanaka. Exact non-identity check is NQP-complete. IJQI 8(5), 2010. arXiv:0903.0675
74. van de Wetering, Amy. Optimising quantum circuits is generally hard. arXiv:2310.05958
75. Kjelstrøm, Pavlogiannis, van de Pol. arXiv:2510.16420
76. Li, Guan. Minimum CNOT synthesis is NP-complete. arXiv:2609.04160 (preprint)
77. Beverland, Campbell, Howard, Kliuchnikov. Lower bounds on the non-Clifford resources for quantum computations. QST 5, 035009 (2020). arXiv:1904.01124
78. Haferkamp et al. Linear growth of quantum circuit complexity. Nature Physics 18, 528 (2022). arXiv:2106.05305
79. Paulihedral, ASPLOS 2022, arXiv:2109.03371; Tetris, ISCA 2024, arXiv:2309.01905; Rustiq, arXiv:2404.03280; QuCLEAR, arXiv:2408.13316; Symphony, arXiv:2608.11579
