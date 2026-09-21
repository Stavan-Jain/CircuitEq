#!/usr/bin/env python3
"""Real Clifford+T circuits for the benchmark ladder: fetch, translate, verify.

The catalogue under ``benchmarks/circuits/`` lists circuits from public suites
(the Feynman benchmarks, QASMBench, the TZAP corpora, QECUnitaryCircuits, the
optimiser outputs published in the PyZX repository) and from parametric
generators. This script is how they get here:

* ``fetch`` downloads the plain-text circuit files and the licence files named
  by the tables below into a cache outside the repository
  (``~/.circuiteq-harness/circuit-cache``, or ``CIRCUITEQ_CIRCUIT_CACHE``), one
  pinned commit per source, and compares every file with the ``sha256`` that
  ``benchmarks/circuits/manifest.json`` records. Nothing is executed and
  nothing else is downloaded.
* ``translate`` turns a source file into the library's gate strings (``H 0``,
  ``CX 1 3``, …) and writes one JSON per circuit with ``name, qubits, gates,
  family, size, source``. The translation is exact or it is refused: ``cz``,
  ``ccx``, ``ccz``, ``swap`` and ``cswap`` by fixed Clifford+T identities,
  ``u1``/``p``/``rz`` only at multiples of ``pi/4`` and read as ``diag(1,
  exp(i*k*pi/4))`` (the convention of ``check_pyzx_benchmarks.py``; Qiskit's
  ``rz`` differs from it by the global phase ``exp(-i*k*pi/8)``, so a file
  that uses ``rz`` is flagged), terminal measurements and barriers dropped and
  counted. Any other gate or angle, ``reset``, classical control, or a gate
  after a measurement of its qubit refuses the file with a reason.
* Every translation is checked numerically against the source gates applied
  natively (a Toffoli as a permutation, a ``cz`` as a sign), including the
  global phase: the full unitary up to 10 qubits, random state vectors up to
  24 qubits within a work budget, beyond that a sparse simulation on sixteen
  random basis inputs while the state stays sparse, and otherwise the gate
  bookkeeping only (the record says which). Where TZAP ships its own
  pre-decomposed copy of a Feynman file, the two gate lists are also compared
  gate by gate, and where pyzx is importable PyZX's parser reads the file too.
* ``catalogue`` recomputes all of it and writes ``manifest.json``; ``--table``
  prints the Markdown rows of ``benchmarks/circuits/README.md``.

Pure Python; numpy is needed only for the numeric checks. Nothing here is
trusted: the Lean kernel judges every pair made from these circuits.

Usage::

    python3 scripts/circuit_sources.py --self-test
    python3 scripts/circuit_sources.py fetch                 # tiers 1 to 3
    python3 scripts/circuit_sources.py fetch --all           # and the large files
    python3 scripts/circuit_sources.py translate feynman_tof_5 --out DIR
    python3 scripts/circuit_sources.py catalogue --write
    python3 scripts/circuit_sources.py catalogue --table
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from fractions import Fraction
from pathlib import Path

try:  # only the numeric checks need it
    import numpy as np
except ImportError:  # pragma: no cover
    np = None

ROOT = Path(__file__).resolve().parents[1]
CATALOGUE = ROOT / "benchmarks" / "circuits"
MANIFEST = CATALOGUE / "manifest.json"

ALPHABET = ("H", "X", "Y", "Z", "S", "Sdg", "T", "Tdg", "CX")
CLIFFORD = {"H", "X", "Y", "Z", "S", "Sdg", "CX"}
CX_DIAGONAL = {"CX", "Z", "S", "Sdg", "T", "Tdg"}
# diag(1, exp(i*k*pi/4)) as gates of the alphabet, in time order; the table of
# `check_pyzx_benchmarks.py`.
PHASES = {0: [], 1: ["T"], 2: ["S"], 3: ["S", "T"], 4: ["Z"], 5: ["Z", "T"], 6: ["Sdg"],
          7: ["Tdg"]}
INVERSE = {"H": "H", "X": "X", "Y": "Y", "Z": "Z", "S": "Sdg", "Sdg": "S", "T": "Tdg",
           "Tdg": "T"}

# Tier bounds: (qubits, gates), both inclusive; tier 4 is everything beyond.
TIERS = ((10, 200), (30, 2000), (100, 20000))

# Numeric checks: the full unitary up to this width, random states up to the
# next, and only while `gates * 2^n` stays within the work budget (numpy moves
# about 5e8 amplitudes a second here, so the budget is two minutes).
UNITARY_MAX_QUBITS = 10
STATE_MAX_QUBITS = 24
WORK_BUDGET = 6e10

Gate = tuple  # (name, wires): ("H", (3,)) or ("CX", (1, 3)), as in `tcount_survey.py`


class Rejected(ValueError):
    """The source is not exactly expressible in the alphabet; the message says why."""


def cache_dir() -> Path:
    return Path(os.environ.get("CIRCUITEQ_CIRCUIT_CACHE",
                               "~/.circuiteq-harness/circuit-cache")).expanduser()


# --------------------------------------------------------------------------
# Sources and circuits
# --------------------------------------------------------------------------

SOURCES = {
    "feynman": {
        "url": "https://github.com/meamy/feynman",
        "commit": "d2c382a2ab43a40a87f12f4255645bbb55f704f8",
        "licence": "BSD-3-Clause",
        "licence_path": "LICENSE.md",
        "redistribution": "allowed; keep the copyright notice and the disclaimer",
        "about": "The Feynman / T-par benchmark suite (Amy, Maslov, Mosca): arithmetic and "
                 "reversible-logic circuits used across the T-count literature. "
                 "`benchmarks/qasm/*.qasm`, written with `ccx`.",
    },
    "tzap": {
        "url": "https://github.com/qqq-wisc/tzap",
        "commit": "077b7a78a936470d6e91da18f8ae1903d1ddebd3",
        "licence": "Apache-2.0",
        "licence_path": "LICENSE",
        "redistribution": "allowed; keep the licence and state changes",
        "about": "TZAP's benchmark corpora: a pre-decomposed copy of the Feynman suite (used "
                 "here as a cross-check of the translation), block-encoding circuits from "
                 "Cobble after Rz synthesis, and large synthesised QFTs.",
    },
    "qasmbench": {
        "url": "https://github.com/pnnl/QASMBench",
        "commit": "357b942396d5c2b7cbc1c229c585a6ef5ccaebac",
        "licence": "BSD-style (Battelle Memorial Institute, 2020)",
        "licence_path": "LICENSE",
        "redistribution": "allowed; keep the copyright notice and the disclaimers",
        "about": "QASMBench (Li, Stein, Krishnamoorthy, Ang): only the files that are exactly "
                 "Clifford+T once `ccx`, `cz`, `swap`, `cswap` and gate definitions are "
                 "expanded and terminal measurements are dropped.",
    },
    "qec": {
        "url": "https://github.com/Stavan-Jain/QECUnitaryCircuits",
        "commit": "3d96b5fe14a393f8eeefe02f45e5d23916b85a4d",
        "licence": "none stated (the repository of this project's author)",
        "licence_path": None,
        "redistribution": "not vendored here beyond the three files already under benchmarks/",
        "about": "Nineteen purely unitary QEC circuits: encoders, cat and GHZ states, "
                 "transversal gates.",
    },
    "pyzx_repo": {
        "url": "https://github.com/zxcalc/pyzx",
        "commit": "ad022cf1d9041bb320656f208bfd0ffdaa8599d8",
        "licence": "Apache-2.0",
        "licence_path": "LICENSE",
        "redistribution": "PyZX's own outputs: allowed. The Nam et al. files come from "
                          "github.com/njross/optimizer, which has no licence file, and the "
                          "T-par outputs from a GPL-3.0 tool: fetched, never vendored",
        "about": "Published optimiser outputs for the Feynman suite, kept in the PyZX "
                 "repository: Nam–Ross–Su–Childs–Maslov light and heavy, T-par, PyZX.",
    },
    "generated": {
        "url": "scripts/circuit_sources.py",
        "commit": None,
        "licence": "this repository's",
        "licence_path": None,
        "redistribution": "generated on demand",
        "about": "Parametric textbook constructions, generated at any size.",
    },
}


def _spec(name, source, path, fmt, family, size, note=""):
    return {"name": name, "source": source, "path": path, "format": fmt, "family": family,
            "size": size, "note": note}


def _clean(stem: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", stem).strip("_")


FEYNMAN = [
    ("tof_3", "tof", 3), ("tof_4", "tof", 4), ("tof_5", "tof", 5), ("tof_10", "tof", 10),
    ("barenco_tof_3", "barenco_tof", 3), ("barenco_tof_4", "barenco_tof", 4),
    ("barenco_tof_5", "barenco_tof", 5), ("barenco_tof_10", "barenco_tof", 10),
    ("mod5_4", "mod5", 4), ("vbe_adder_3", "vbe_adder", 3), ("rc_adder_6", "rc_adder", 6),
    ("adder_8", "adder", 8), ("qcla_adder_10", "qcla_adder", 10), ("qcla_com_7", "qcla_com", 7),
    ("qcla_mod_7", "qcla_mod", 7), ("csla_mux_3", "csla_mux", 3), ("csum_mux_9", "csum_mux", 9),
    ("mod_mult_55", "mod_mult", 55), ("mod_red_21", "mod_red", 21),
    ("mod_adder_1024", "mod_adder", 1024), ("mod_adder_1048576", "mod_adder", 1048576),
    ("gf2^4_mult", "gf2_mult", 4), ("gf2^5_mult", "gf2_mult", 5), ("gf2^6_mult", "gf2_mult", 6),
    ("gf2^7_mult", "gf2_mult", 7), ("gf2^8_mult", "gf2_mult", 8), ("gf2^9_mult", "gf2_mult", 9),
    ("gf2^10_mult", "gf2_mult", 10), ("gf2^16_mult", "gf2_mult", 16),
    ("gf2^32_mult", "gf2_mult", 32), ("gf2^64_mult", "gf2_mult", 64),
    ("gf2^128_mult", "gf2_mult", 128), ("gf2^256_mult", "gf2_mult", 256),
    ("hwb6", "hwb", 6), ("hwb8", "hwb", 8), ("hwb10", "hwb", 10), ("hwb11", "hwb", 11),
    ("hwb12", "hwb", 12), ("ham15-low", "ham15", "low"), ("ham15-med", "ham15", "med"),
    ("ham15-high", "ham15", "high"), ("grover_5", "grover", 5), ("qft_4", "qft", 4),
    ("cycle_17_3", "cycle", 17),
]

# QASMBench files whose gate names are all in the alphabet's reach; the parser
# still decides (a gate after a measurement of its qubit refuses the file).
QASMBENCH = [
    ("small/adder_n4", "qb_adder", 4), ("small/adder_n10", "qb_adder", 10),
    ("large/adder_n28", "qb_adder", 28), ("large/adder_n64", "qb_adder", 64),
    ("large/adder_n118", "qb_adder", 118), ("large/adder_n433", "qb_adder", 433),
    ("medium/multiplier_n15", "qb_multiplier", 15), ("large/multiplier_n45", "qb_multiplier", 45),
    ("large/multiplier_n75", "qb_multiplier", 75),
    ("large/multiplier_n350", "qb_multiplier", 350),
    ("large/multiplier_n400", "qb_multiplier", 400),
    ("medium/multiply_n13", "qb_multiply", 13), ("medium/bigadder_n18", "qb_bigadder", 18),
    ("medium/bv_n14", "qb_bv", 14), ("medium/bv_n19", "qb_bv", 19), ("large/bv_n30", "qb_bv", 30),
    ("large/bv_n70", "qb_bv", 70), ("large/bv_n140", "qb_bv", 140),
    ("large/bv_n280", "qb_bv", 280),
    ("small/cat_state_n4", "qb_cat", 4), ("medium/cat_state_n22", "qb_cat", 22),
    ("large/cat_n35", "qb_cat", 35), ("large/cat_n65", "qb_cat", 65),
    ("large/cat_n130", "qb_cat", 130), ("large/cat_n260", "qb_cat", 260),
    ("medium/ghz_state_n23", "qb_ghz", 23), ("large/ghz_n40", "qb_ghz", 40),
    ("large/ghz_n78", "qb_ghz", 78), ("large/ghz_n127", "qb_ghz", 127),
    ("large/ghz_n255/ghz_state_n255", "qb_ghz", 255),
    ("medium/qram_n20", "qb_qram", 20), ("small/sat_n7", "qb_sat", 7),
    ("medium/sat_n11", "qb_sat", 11), ("medium/qec9xz_n17", "qb_qec9xz", 17),
    ("medium/seca_n11", "qb_seca", 11), ("small/qec_en_n5", "qb_qec_en", 5),
    ("small/error_correctiond3_n5", "qb_error_correctiond3", 5),
    ("small/toffoli_n3", "qb_toffoli", 3), ("small/fredkin_n3", "qb_fredkin", 3),
    ("small/grover_n2", "qb_grover", 2), ("small/hs4_n4", "qb_hs4", 4),
    ("small/simon_n6", "qb_simon", 6), ("small/lpn_n5", "qb_lpn", 5),
    ("small/bb84_n8", "qb_bb84", 8), ("small/teleportation_n3", "qb_teleportation", 3),
    ("small/deutsch_n2", "qb_deutsch", 2), ("small/iswap_n2", "qb_iswap", 2),
    ("small/qrng_n4", "qb_qrng", 4),
]

QEC = [
    ("cat3_prep", "qec_cat", 3), ("cat4_prep", "qec_cat", 4), ("cat5_prep", "qec_cat", 5),
    ("cat7_prep", "qec_cat", 7), ("ghz5_fanout", "qec_ghz_fanout", 5),
    ("rep3_bitflip_encode", "qec_rep3", 3), ("rep3_phaseflip_encode", "qec_rep3", 3),
    ("code_422_encode_00L", "qec_encoder", 4), ("code_513_encode_0L", "qec_encoder", 5),
    ("steane_713_encode_0L", "qec_encoder", 7), ("steane_713_encode_plusL", "qec_encoder", 7),
    ("steane_713_H_nf_fig4", "qec_encoder", 7), ("code_833_encode_basis", "qec_encoder", 8),
    ("shor_913_encode", "qec_encoder", 9), ("rm15_1531_encode_0L", "qec_encoder", 15),
    ("steane_713_transversal_H", "qec_transversal", 7),
    ("steane_713_transversal_S", "qec_transversal", 7),
    ("steane_713_transversal_CNOT", "qec_transversal", 14),
    ("rm15_1531_transversal_Tdg", "qec_transversal", 15),
]

TZAP_LARGE = [
    ("cobble-t/laplacian-filter", "cobble", 11), ("cobble-t/matrix-inversion", "cobble", 12),
    ("cobble-t/chebyshev", "cobble", 14), ("cobble-t/hamiltonian-simulation", "cobble", 16),
    ("cobble-t/spectral-thresholding", "cobble", 16), ("cobble-t/ols-ridge", "cobble", 22),
    ("qft/qft_q020_d32421", "synth_qft", 20), ("qft/qft_q030_d50671", "synth_qft", 30),
    ("qft/qft_q040_d68921", "synth_qft", 40), ("qft/qft_q050_d87171", "synth_qft", 50),
]

# Generated rungs: (family, size). Any other size works from the command line
# as `gen_<family>_<size>`.
GENERATED = [
    ("tof", 3), ("tof", 5), ("tof", 8), ("tof", 16), ("tof", 32), ("tof", 50), ("tof", 100),
    ("barenco_tof", 3), ("barenco_tof", 5), ("barenco_tof", 10), ("barenco_tof", 16),
    ("barenco_tof", 50), ("barenco_tof", 100),
    ("cuccaro", 2), ("cuccaro", 4), ("cuccaro", 8), ("cuccaro", 14), ("cuccaro", 32),
    ("cuccaro", 49), ("cuccaro", 128), ("cuccaro", 512),
    ("ghz", 5), ("ghz", 20), ("ghz", 100), ("ghz", 1000),
    ("surface", 3), ("surface", 5), ("surface", 7), ("surface", 9), ("surface", 15),
]

# The published optimiser outputs in the PyZX repository, by base name: the
# `_before` file of Nam et al. is the original, the others are twins of it.
PUBLISHED_BASES = [
    "tof_3", "tof_4", "tof_5", "tof_10", "barenco_tof_3", "barenco_tof_4", "barenco_tof_5",
    "barenco_tof_10", "mod5_4", "vbe_adder_3", "rc_adder_6", "adder_8", "qcla_adder_10",
    "qcla_com_7", "qcla_mod_7", "csla_mux_3", "csum_mux_9", "mod_mult_55", "mod_red_21",
    "mod_adder_1024", "gf2^4_mult", "gf2^5_mult", "gf2^6_mult", "gf2^7_mult", "gf2^8_mult",
    "gf2^9_mult", "gf2^10_mult", "gf2^16_mult",
]
# Nam et al. renamed two inputs.
_NAM_STEM = {"csla_mux_3": "csla_mux_3_original", "csum_mux_9": "csum_mux_9_corrected"}
PUBLISHED_KINDS = {
    "before": ("circuits/Arithmetic_and_Toffoli/{nam}_before", "quipper",
               "the input of Nam et al. (from the T-par repository)"),
    "nam_light": ("circuits/Arithmetic_and_Toffoli/{nam}_after_light", "quipper",
                  "Nam–Ross–Su–Childs–Maslov, light optimisation"),
    "nam_heavy": ("circuits/Arithmetic_and_Toffoli/{nam}_after_heavy", "quipper",
                  "Nam–Ross–Su–Childs–Maslov, heavy optimisation"),
    "tpar": ("circuits/Arithmetic_and_Toffoli/{base}_tpar.qc", "qc",
             "T-par (Amy, Maslov, Mosca); may assume that ancillas start in |0>"),
    "pyzx": ("circuits/optimized/{nam}_pyzx.qc", "qc",
             "PyZX's published output (Kissinger, van de Wetering)"),
}


def published_spec(base: str, kind: str) -> dict:
    template, fmt, note = PUBLISHED_KINDS[kind]
    path = template.format(base=base, nam=_NAM_STEM.get(base, base))
    return _spec(f"published_{_clean(base)}__{kind}", "pyzx_repo", path, fmt,
                 "published_" + re.sub(r"_?\d+$", "", _clean(base)), kind, note)


def circuit_specs() -> list[dict]:
    """Every circuit of the catalogue, in ladder order within its source."""
    specs = []
    for stem, family, size in FEYNMAN:
        specs.append(_spec("feynman_" + _clean(stem), "feynman", f"benchmarks/qasm/{stem}.qasm",
                           "qasm2", family, size))
    for path, family, size in QASMBENCH:
        parts = path.split("/")
        stem = parts[-1]
        full = path if len(parts) == 3 else f"{path}/{stem}"
        specs.append(_spec("qasmbench_" + _clean(parts[1]), "qasmbench", full + ".qasm", "qasm2",
                           family, size))
    for stem, family, size in QEC:
        specs.append(_spec("qec_" + _clean(stem), "qec", f"qec_circuits/{stem}.qasm", "qasm2",
                           family, size))
    for path, family, size in TZAP_LARGE:
        specs.append(_spec("tzap_" + _clean(path), "tzap", f"benchmarks/{path}.qasm", "qasm2",
                           family, size))
    for family, size in GENERATED:
        specs.append(_spec(f"gen_{family}_{size}", "generated", None, "generator",
                           "gen_" + family, size))
    return specs


def published_specs() -> list[dict]:
    return [published_spec(b, k) for b in PUBLISHED_BASES for k in PUBLISHED_KINDS]


def find_spec(name: str) -> dict:
    for s in circuit_specs() + published_specs():
        if s["name"] == name:
            return s
    m = re.fullmatch(r"gen_([a-z_]+?)_(\d+)", name)
    if m and m[1] in GENERATORS:
        return _spec(name, "generated", None, "generator", "gen_" + m[1], int(m[2]))
    raise KeyError(f"no circuit named `{name}`")


# Surveyed and refused without being listed above, with the reason. Files the
# parser refuses itself are added to the manifest's `rejected` list as well.
SURVEY_REJECTED = [
    ("feynman", "benchmarks/qc/fprenorm.qc", "only in .qc form, which is not the form the "
     "optimisers under comparison read; the other 44 circuits have a .qasm"),
    ("feynman", "benchmarks/qasm3/*.qasm", "OpenQASM 3 programs with loops, reset and "
     "measurement-controlled gates"),
    ("tzap", "benchmarks/cobble-rz/*.qasm", "122 to 910 `rz` rotations per circuit at angles "
     "that are not multiples of pi/4"),
    # QASMBench: every file under 1.5 MB was run through the parser; the reason
    # is the first one it met.
    ("qasmbench", "dnn_n33, dnn_n51, knn_n25, knn_n31, knn_n41, knn_n67, knn_n129, knn_n341, "
     "qugan_n39, qugan_n71, qugan_n111, qugan_n395, wstate_n27, wstate_n36, wstate_n76, "
     "wstate_n118, wstate_n380, hhl_n7", "`ry` rotations"),
    ("qasmbench", "QAOA_3SAT_N1000_p1, ising_n10, ising_n26, ising_n34, ising_n42, ising_n66, "
     "ising_n98, ising_n420, basis_trotter_n4 (both files), qaoa_n3, qaoa_n6, variational_n4, "
     "vqe_uccsd_n4, vqe_uccsd_n6, vqe_uccsd_n8", "`rz` at angles that are not multiples of pi/4"),
    ("qasmbench", "swap_test_n25, swap_test_n41, swap_test_n83, swap_test_n115, swap_test_n361, "
     "dnn_n2, dnn_n8, dnn_n16, bell_n4", "`rx` rotations"),
    ("qasmbench", "cc_n12, cc_n32, cc_n64, cc_n151, cc_n301, inverseqft_n4, qec_sm_n5",
     "classical control (`if`)"),
    ("qasmbench", "qft_n18, qft_n29, qft_n63, qft_n160, ipea_n2, pea_n5",
     "`u1` at angles that are not multiples of pi/4"),
    ("qasmbench", "QV_n32, basis_change_n3, linearsolver_n3, quantumwalks_n2, wstate_n3",
     "`u3` gates"),
    ("qasmbench", "square_root_n18, square_root_n45, bwt_n21, shor_n5", "`reset`"),
    ("qasmbench", "qf21_n15, qft_n4, qpe_n9", "`cu1` (controlled phases finer than pi/4)"),
    ("qasmbench", "gcm_n13, vqe_n4", "`sx` and `rz` at arbitrary angles"),
    ("qasmbench", "hhl_n10, hhl_n14, vqe_n24, vqe_uccsd_n28, factor247_n15, bwt_n37, bwt_n57, "
     "bwt_n97, bwt_n177, qft_n320, QV_n100, QAOA_3SAT_N100_p100, QAOA_3SAT_N10000_p1, "
     "square_root_n60", "not examined: over 1.5 MB each; every smaller member of these "
     "families is refused above"),
    ("qasmbench", "*_transpiled.qasm", "the transpiled variants are in IBM's basis (`rz`, "
     "`sx`), not the originals"),
    ("pyzx_repo", "circuits/QFT_and_Adders/*, circuits/PF/*", "`QRot` rotations at angles "
     "beyond pi/4"),
    ("revlib", "www.revlib.org", "not fetched: the site offers no stable per-file URLs or "
     "commit to pin and no licence statement; its hwb, ham and cycle functions are covered "
     "by the Feynman suite's copies"),
]


# --------------------------------------------------------------------------
# Native operations and their exact translations
# --------------------------------------------------------------------------
#
# A parsed source is a list of native operations `(name, wires)` or
# `("phase", wires, k)` for diag(1, exp(i*k*pi/4)). `translate` maps each to
# gates of the alphabet on the same wires; `self_test` checks every rule
# against the native matrix, global phase included.

ONE_QUBIT = {"h": "H", "x": "X", "y": "Y", "z": "Z", "s": "S", "sdg": "Sdg", "t": "T",
             "tdg": "Tdg"}
NATIVE_ARITY = {**{k: 1 for k in ONE_QUBIT}, "phase": 1, "cx": 2, "cz": 2, "swap": 2, "ccx": 3,
                "ccz": 3, "ccz_dg": 3, "cswap": 3}


def one(name: str, i: int) -> Gate:
    return (name, (i,))


def cx(c: int, t: int) -> Gate:
    return ("CX", (c, t))


def ccx_gates(a: int, b: int, c: int) -> list[Gate]:
    """The seven-``T`` Toffoli of ``qelib1.inc``, exact including the phase."""
    return [one("H", c), cx(b, c), one("Tdg", c), cx(a, c), one("T", c), cx(b, c),
            one("Tdg", c), cx(a, c), one("T", b), one("T", c), one("H", c), cx(a, b),
            one("T", a), one("Tdg", b), cx(a, b)]


def ccz_gates(a: int, b: int, c: int) -> list[Gate]:
    """The seven-``T`` doubly-controlled ``Z``: the Toffoli without its Hadamards."""
    return [cx(b, c), one("Tdg", c), cx(a, c), one("T", c), cx(b, c), one("Tdg", c), cx(a, c),
            one("T", b), one("T", c), cx(a, b), one("T", a), one("Tdg", b), cx(a, b)]


def inverse_gates(gates: list[Gate]) -> list[Gate]:
    return [(INVERSE.get(name, name), w) for name, w in reversed(gates)]


def translate_op(op: tuple) -> list[Gate]:
    """One native operation as gates of the alphabet."""
    name, w = op[0], op[1]
    if name in ONE_QUBIT:
        return [one(ONE_QUBIT[name], w[0])]
    if name == "phase":
        return [one(g, w[0]) for g in PHASES[op[2] % 8]]
    if name == "cx":
        return [cx(*w)]
    if name == "cz":
        return [one("H", w[1]), cx(w[0], w[1]), one("H", w[1])]
    if name == "swap":
        return [cx(w[0], w[1]), cx(w[1], w[0]), cx(w[0], w[1])]
    if name == "ccx":
        return ccx_gates(*w)
    if name == "ccz":
        return ccz_gates(*w)
    if name == "ccz_dg":
        return inverse_gates(ccz_gates(*w))
    if name == "cswap":
        return [cx(w[2], w[1])] + ccx_gates(w[0], w[1], w[2]) + [cx(w[2], w[1])]
    raise Rejected(f"no exact translation for `{name}`")


def translate(ops: list[tuple]) -> list[Gate]:
    return [g for op in ops for g in translate_op(op)]


def show(g: Gate) -> str:
    return " ".join([g[0], *map(str, g[1])])


def parse_gates(strings: list[str]) -> list[Gate]:
    out = []
    for s in strings:
        name, *wires = s.split()
        out.append((name, tuple(int(w) for w in wires)))
    return out


def _check_op(name: str, wires: tuple, n: int, where: str) -> None:
    if len(wires) != NATIVE_ARITY[name]:
        raise Rejected(f"{where}: `{name}` on {len(wires)} wires")
    if len(set(wires)) != len(wires):
        raise Rejected(f"{where}: `{name}` with a repeated wire {wires}")
    if any(not 0 <= w < n for w in wires):
        raise Rejected(f"{where}: wire out of range in `{name}` {wires}")


# --------------------------------------------------------------------------
# Angles: rational multiples of pi, or refused
# --------------------------------------------------------------------------

def _angle(node: ast.AST, env: dict) -> tuple[Fraction, Fraction]:
    """An angle expression as ``(a, b)`` meaning ``a*pi + b``, exactly."""
    if isinstance(node, ast.Expression):
        return _angle(node.body, env)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
        return Fraction(0), Fraction(str(node.value))
    if isinstance(node, ast.Name):
        if node.id == "pi":
            return Fraction(1), Fraction(0)
        if node.id in env:
            return env[node.id]
        raise Rejected(f"unknown name `{node.id}` in an angle")
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        a, b = _angle(node.operand, env)
        return (-a, -b) if isinstance(node.op, ast.USub) else (a, b)
    if isinstance(node, ast.BinOp):
        (a, b), (c, d) = _angle(node.left, env), _angle(node.right, env)
        if isinstance(node.op, ast.Add):
            return a + c, b + d
        if isinstance(node.op, ast.Sub):
            return a - c, b - d
        if isinstance(node.op, ast.Mult) and (a == 0 or c == 0):
            return a * d + c * b, b * d
        if isinstance(node.op, ast.Div) and c == 0 and d != 0:
            return a / d, b / d
    raise Rejected("an angle that is not a rational expression in pi")


def eval_angle(text: str, env: dict | None = None) -> tuple[Fraction, Fraction]:
    try:
        tree = ast.parse(text.strip(), mode="eval")
    except SyntaxError as e:
        raise Rejected(f"cannot read the angle `{text.strip()}`") from e
    return _angle(tree, env or {})


def quarter_turns(angle: tuple[Fraction, Fraction], gate: str) -> int:
    a, b = angle
    if b != 0 or (4 * a).denominator != 1:
        shown = f"{a}*pi" + (f" + {float(b)}" if b else "")
        raise Rejected(f"`{gate}` at {shown}, not a multiple of pi/4")
    return int(4 * a) % 8


# --------------------------------------------------------------------------
# OpenQASM 2.0
# --------------------------------------------------------------------------

QASM_NATIVE = {**{k: k for k in ONE_QUBIT}, "cx": "cx", "CX": "cx", "cz": "cz", "swap": "swap",
               "ccx": "ccx", "ccz": "ccz", "cswap": "cswap"}
QASM_PHASE = {"u1", "p", "rz"}
_APPLY = re.compile(r"^([A-Za-z_]\w*)\s*(?:\((.*)\))?\s*(.*)$", re.S)
_GATEDEF = re.compile(r"\bgate\s+([A-Za-z_]\w*)\s*(?:\(([^)]*)\))?\s*([^{]*?)\{([^}]*)\}", re.S)


def _split_args(text: str) -> list[str]:
    return [a.strip() for a in text.split(",") if a.strip()]


def _split_params(text: str) -> list[str]:
    """Split on top-level commas only."""
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
            continue
        depth += ch == "("
        depth -= ch == ")"
        cur += ch
    return [p for p in out + [cur] if p.strip()]


def parse_qasm(text: str) -> dict:
    """An OpenQASM 2.0 program as native operations, or ``Rejected``.

    Returns ``qubits``, ``ops``, ``dropped`` (counts of what was left out
    without changing the unitary: barriers, ``id`` gates, terminal
    measurements), ``registers``, ``uses_rz`` and ``notes``.
    """
    text = re.sub(r"//[^\n]*", "", text)
    if re.search(r"\bopaque\b", text):
        raise Rejected("an `opaque` gate")
    defs: dict[str, tuple[list[str], list[str], list[str]]] = {}
    for m in _GATEDEF.finditer(text):
        defs[m[1]] = (_split_args(m[2] or ""), _split_args(m[3]),
                      [s.strip() for s in m[4].split(";") if s.strip()])
    text = _GATEDEF.sub("", text)

    registers: dict[str, tuple[int, int]] = {}
    n = 0
    ops: list[tuple] = []
    dropped = {"barrier": 0, "id": 0, "measure": 0}
    notes: list[str] = []
    measured: set[int] = set()
    uses: set[str] = set()
    saw_header = False

    def wires_of(arg: str, where: str) -> list[int]:
        m = re.fullmatch(r"([A-Za-z_]\w*)\s*(?:\[\s*(\d+)\s*\])?", arg)
        if not m or m[1] not in registers:
            raise Rejected(f"{where}: cannot read the argument `{arg}`")
        start, size = registers[m[1]]
        if m[2] is None:
            return list(range(start, start + size))
        if int(m[2]) >= size:
            raise Rejected(f"{where}: `{arg}` is off its register")
        return [start + int(m[2])]

    def emit(name: str, params: list, wires: tuple, where: str, depth: int = 0) -> None:
        if depth > 32:
            raise Rejected(f"{where}: gate definitions nest too deeply")
        if name == "id":
            dropped["id"] += 1
            return
        if name in defs and name not in QASM_NATIVE:
            formals, qargs, body = defs[name]
            if len(formals) != len(params) or len(qargs) != len(wires):
                raise Rejected(f"{where}: `{name}` applied with the wrong number of arguments")
            env = dict(zip(formals, params))
            bind = dict(zip(qargs, wires))
            for stmt in body:
                m = _APPLY.match(stmt)
                if m[1] == "barrier":
                    continue
                inner = [_angle(ast.parse(p.strip(), mode="eval"), env)
                         for p in _split_params(m[2] or "")]
                try:
                    inner_wires = tuple(bind[a] for a in _split_args(m[3]))
                except KeyError as e:
                    raise Rejected(f"{where}: `{name}` uses the undeclared qubit {e}") from e
                emit(m[1], inner, inner_wires, f"{where} (in `{name}`)", depth + 1)
            return
        if any(w in measured for w in wires):
            raise Rejected(f"{where}: `{name}` acts on a qubit after it was measured "
                           "(a measurement that is not terminal)")
        if name in QASM_PHASE:
            if len(params) != 1 or len(wires) != 1:
                raise Rejected(f"{where}: `{name}` takes one angle and one qubit")
            uses.add(name)
            k = quarter_turns(params[0], name)
            if k:
                ops.append(("phase", wires, k))
            return
        if name not in QASM_NATIVE:
            raise Rejected(f"{where}: the gate `{name}` is outside the alphabet's reach")
        if params:
            raise Rejected(f"{where}: `{name}` takes no angle")
        native = QASM_NATIVE[name]
        _check_op(native, wires, n, where)
        ops.append((native, wires))

    for k, stmt in enumerate(s.strip() for s in text.split(";")):
        if not stmt:
            continue
        where = f"statement {k + 1}"
        if stmt.startswith("OPENQASM"):
            saw_header = True
            if not re.fullmatch(r"OPENQASM\s+2(\.0)?", stmt):
                raise Rejected(f"`{stmt}`: only OpenQASM 2.0 is read")
            continue
        if stmt.startswith("include"):
            if "qelib1.inc" not in stmt:
                raise Rejected(f"`{stmt}`: only qelib1.inc is known")
            continue
        m = re.fullmatch(r"(qreg|creg)\s+([A-Za-z_]\w*)\s*\[\s*(\d+)\s*\]", stmt)
        if m:
            if m[1] == "qreg":
                registers[m[2]] = (n, int(m[3]))
                n += int(m[3])
            continue
        if re.match(r"(if\s*\(|reset\b)", stmt):
            raise Rejected(f"{where}: `{stmt.split()[0].split('(')[0]}` (classical control or "
                           "reset) is not unitary")
        if stmt.startswith("barrier"):
            dropped["barrier"] += 1
            continue
        if stmt.startswith("measure"):
            m = re.fullmatch(r"measure\s+(.+?)\s*->\s*(.+)", stmt, re.S)
            if not m:
                raise Rejected(f"{where}: cannot read `{stmt}`")
            for w in wires_of(m[1].strip(), where):
                measured.add(w)
                dropped["measure"] += 1
            continue
        m = _APPLY.match(stmt)
        if not m:
            raise Rejected(f"{where}: cannot read `{stmt}`")
        params = [eval_angle(p) for p in _split_params(m[2] or "")]
        groups = [wires_of(a, where) for a in _split_args(m[3])]
        if not groups:
            raise Rejected(f"{where}: `{stmt}` has no qubit argument")
        width = max(len(g) for g in groups)
        if any(len(g) not in (1, width) for g in groups):
            raise Rejected(f"{where}: registers of different sizes in `{stmt}`")
        for j in range(width):
            emit(m[1], params, tuple(g[j] if len(g) > 1 else g[0] for g in groups), where)
    if not saw_header:
        notes.append("no OPENQASM header line")
    if n == 0:
        raise Rejected("no quantum register")
    return {"qubits": n, "ops": ops, "dropped": {k: v for k, v in dropped.items() if v},
            "registers": {k: list(v) for k, v in registers.items()}, "uses_rz": "rz" in uses,
            "phase_gates": sorted(uses), "notes": notes}


# --------------------------------------------------------------------------
# The .qc format (Feynman, T-par, PyZX) and Quipper ASCII (Nam et al.)
# --------------------------------------------------------------------------

def parse_qc(text: str) -> dict:
    """A ``.qc`` circuit: wire ``k`` is the ``k``-th name of the ``.v`` line."""
    names: list[str] = []
    inputs: list[str] | None = None
    ops: list[tuple] = []
    body = False
    for k, raw in enumerate(text.splitlines()):
        line = raw.split("#")[0].strip()
        if not line:
            continue
        where = f"line {k + 1}"
        if line.startswith(".v"):
            names += line.split()[1:]
            continue
        if line.startswith(".i"):
            inputs = (inputs or []) + line.split()[1:]
            continue
        if line.startswith("."):
            continue
        if line.upper().startswith("BEGIN"):
            if line.strip().upper() != "BEGIN":
                raise Rejected(f"{where}: sub-circuit definitions are not read")
            body = True
            continue
        if line.upper() == "END":
            body = False
            continue
        if not body:
            raise Rejected(f"{where}: `{line}` outside BEGIN … END")
        head, *args = line.split()
        try:
            w = tuple(names.index(a) for a in args)
        except ValueError as e:
            raise Rejected(f"{where}: undeclared qubit in `{line}`") from e
        low, n = head.lower(), len(w)
        if low in ("tof", "cnot", "not", "x") and 1 <= n <= 3:
            op = (("x", "cx", "ccx")[n - 1], w)
        elif low in ("z", "cz", "zd") and 1 <= n <= 3:
            op = (("z", "cz", "ccz_dg" if low == "zd" else "ccz")[n - 1], w)
        elif low in ("h", "y") and n == 1:
            op = (low, w)
        elif low in ("t", "t*", "p", "p*", "s", "s*") and n == 1:
            op = ({"t": "t", "t*": "tdg", "p": "s", "p*": "sdg", "s": "s", "s*": "sdg"}[low], w)
        elif low == "swap" and n == 2:
            op = ("swap", w)
        else:
            raise Rejected(f"{where}: `{head}` on {n} qubits has no exact translation without "
                           "an ancilla" if low in ("tof", "z", "zd") else
                           f"{where}: unknown gate `{head}`")
        _check_op(op[0], op[1], len(names), where)
        ops.append(op)
    if not names:
        raise Rejected("no `.v` line")
    zero = [names.index(v) for v in names if inputs is not None and v not in inputs]
    return {"qubits": len(names), "ops": ops, "dropped": {}, "uses_rz": False,
            "zero_wires": zero,
            "notes": [f"wires {zero} are not primary inputs (`.i`): tools that read .qc may "
                      "assume they start in |0>"] if zero else []}


_QGATE = re.compile(r'^QGate\["([^"]+)"\](\*?)\((\d+)\)(?:\s+with controls=\[([^\]]*)\])?'
                    r'(?:\s+with nocontrol)?$')


def parse_quipper(text: str) -> dict:
    """The Quipper ASCII subset of the Nam et al. files."""
    wires: list[int] = []
    ops: list[tuple] = []
    for k, raw in enumerate(text.splitlines()):
        line = raw.strip()
        where = f"line {k + 1}"
        if not line or line.startswith("Outputs:"):
            continue
        if line.startswith("Inputs:"):
            body = line.split(":", 1)[1].strip()
            if body != "None":
                for item in filter(None, (i.strip() for i in body.split(","))):
                    wire, kind = item.split(":")
                    if kind != "Qbit":
                        raise Rejected(f"{where}: a classical wire")
                    wires.append(int(wire))
            continue
        m = _QGATE.match(line)
        if not m:
            raise Rejected(f"{where}: `{line.split('(')[0]}` is not a plain gate (rotation, "
                           "initialisation or comment)")
        name, dagger, target = m[1], bool(m[2]), int(m[3])
        controls = [(c.strip()[0], int(c.strip()[1:])) for c in (m[4] or "").split(",")
                    if c.strip()]
        try:
            w = tuple(wires.index(c) for _, c in controls) + (wires.index(target),)
        except ValueError as e:
            raise Rejected(f"{where}: undeclared wire") from e
        n = len(w)
        if name in ("not", "X") and n <= 3:
            op = (("x", "cx", "ccx")[n - 1], w)
        elif name == "Z" and n <= 3:
            op = (("z", "cz", "ccz")[n - 1], w)
        elif name in ("H", "Y") and n == 1:
            op = (name.lower(), w)
        elif name in ("S", "T") and n == 1:
            op = (name.lower() + ("dg" if dagger else ""), w)
        else:
            raise Rejected(f"{where}: `{name}` with {n - 1} controls has no exact translation")
        negative = [wires.index(c) for sign, c in controls if sign == "-"]
        flips = [("x", (c,)) for c in negative]
        for o in flips + [op] + flips:
            _check_op(o[0], o[1], len(wires), where)
            ops.append(o)
    if not wires:
        raise Rejected("no `Inputs:` line")
    return {"qubits": len(wires), "ops": ops, "dropped": {}, "uses_rz": False, "notes": []}


PARSERS = {"qasm2": parse_qasm, "qc": parse_qc, "quipper": parse_quipper}


# --------------------------------------------------------------------------
# Generators (native operations, so they are verified like the files)
# --------------------------------------------------------------------------

def gen_tof(k: int) -> tuple[int, list[tuple], str]:
    """A ``k``-controlled NOT through ``k - 2`` clean ancillas: ``2k - 3`` Toffolis."""
    if k < 3:
        raise Rejected("tof needs at least three controls")
    ctrl, anc, tgt = list(range(k)), list(range(k, 2 * k - 2)), 2 * k - 2
    chain = [(ctrl[0], ctrl[1], anc[0])] + [(anc[i - 1], ctrl[i + 1], anc[i])
                                            for i in range(1, k - 2)]
    toffolis = chain + [(anc[k - 3], ctrl[k - 1], tgt)] + chain[::-1]
    return 2 * k - 1, [("ccx", t) for t in toffolis], \
        "controls 0..k-1, clean ancillas k..2k-3, target 2k-2; as `tcount_survey.tof`"


def gen_barenco_tof(k: int) -> tuple[int, list[tuple], str]:
    """Barenco et al. (1995), Lemma 7.2: ``4 (k - 2)`` Toffolis, dirty ancillas."""
    if k < 3:
        raise Rejected("barenco_tof needs at least three controls")
    ctrl, anc, tgt = list(range(k)), list(range(k, 2 * k - 2)), 2 * k - 2
    chain = [(ctrl[k - 1], anc[k - 3], tgt)]
    chain += [(ctrl[i + 1], anc[i - 1], anc[i]) for i in range(k - 3, 0, -1)]
    chain += [(ctrl[0], ctrl[1], anc[0])]
    toffolis = chain + chain[-2::-1] + chain[1:] + chain[-2:0:-1]
    return 2 * k - 1, [("ccx", t) for t in toffolis], \
        "same wires as tof; every ancilla is restored; as `tcount_survey.barenco_tof`"


def gen_cuccaro(k: int) -> tuple[int, list[tuple], str]:
    """The Cuccaro–Draper–Kutin–Moulton ripple-carry adder on ``k`` bits."""
    if k < 1:
        raise Rejected("cuccaro needs at least one bit")
    c, z = 0, 2 * k + 1
    b, a = [1 + 2 * i for i in range(k)], [2 + 2 * i for i in range(k)]
    maj = lambda c, b, a: [("cx", (a, b)), ("cx", (a, c)), ("ccx", (c, b, a))]  # noqa: E731
    uma = lambda c, b, a: [("ccx", (c, b, a)), ("cx", (a, c)), ("cx", (c, b))]  # noqa: E731
    ops = maj(c, b[0], a[0])
    for i in range(1, k):
        ops += maj(a[i - 1], b[i], a[i])
    ops += [("cx", (a[k - 1], z))]
    for i in range(k - 1, 0, -1):
        ops += uma(a[i - 1], b[i], a[i])
    ops += uma(c, b[0], a[0])
    return 2 * k + 2, ops, \
        "carry-in 0, b_i = 1+2i, a_i = 2+2i, carry-out 2k+1; as `tcount_survey.cuccaro`"


def gen_ghz(k: int) -> tuple[int, list[tuple], str]:
    """The GHZ ladder ``H 0; CX 0 1; …; CX (k-2) (k-1)``."""
    if k < 2:
        raise Rejected("ghz needs at least two qubits")
    return k, [("h", (0,))] + [("cx", (i, i + 1)) for i in range(k - 1)], "as `scale_test.ghz`"


def surface_stabilizers(d: int) -> list[tuple[str, list[int]]]:
    """The ``d² − 1`` stabilizers of the rotated surface code (``scale_test.py``)."""
    out = []
    for r in range(-1, d):
        for c in range(-1, d):
            qs = [(r + dr) * d + (c + dc) for dr in (0, 1) for dc in (0, 1)
                  if 0 <= r + dr < d and 0 <= c + dc < d]
            kind = "X" if (r + c) % 2 == 0 else "Z"
            boundary = (kind == "X" and r in (-1, d - 1)) or (kind == "Z" and c in (-1, d - 1))
            if len(qs) == 4 or (len(qs) == 2 and boundary):
                out.append((kind, qs))
    assert len(out) == d * d - 1
    return out


def gen_surface(d: int, rounds: int = 2) -> tuple[int, list[tuple], str]:
    """Two rounds of syndrome extraction of the rotated surface code of distance ``d``,
    unitary part only, on ``2 d² − 1`` qubits."""
    if d < 2:
        raise Rejected("surface needs distance at least two")
    ops = []
    for _ in range(rounds):
        for k, (kind, qs) in enumerate(surface_stabilizers(d)):
            a = d * d + k
            if kind == "X":
                ops += [("h", (a,))] + [("cx", (a, q)) for q in qs] + [("h", (a,))]
            else:
                ops += [("cx", (q, a)) for q in qs]
    return 2 * d * d - 1, ops, f"{rounds} rounds, data 0..d²-1, one ancilla per stabilizer; " \
                               "as `scale_test.surface`"


GENERATORS = {"tof": gen_tof, "barenco_tof": gen_barenco_tof, "cuccaro": gen_cuccaro,
              "ghz": gen_ghz, "surface": gen_surface}


# --------------------------------------------------------------------------
# Simulation (untrusted; numpy)
# --------------------------------------------------------------------------
#
# Qubit 0 is the most significant bit, as in `tcount_survey.unitary`. A state
# is a tensor of shape (2,)*n + (columns,); every operation works in place on
# views, so a 24-qubit state costs one array and one half-size temporary.

_R = 0.5 ** 0.5


def _phase(k: int) -> complex:
    return complex(np.exp(1j * np.pi * k / 4))


def _swap(v, i, j) -> None:
    tmp = v[i].copy()
    v[i] = v[j]
    v[j] = tmp


def apply_op(state, op: tuple) -> None:
    """Apply a native operation or a gate of the alphabet, in place."""
    name, w = op[0], op[1]
    v = np.moveaxis(state, w, range(len(w)))
    low = name.lower()
    if low == "h":
        a = v[0].copy()
        v[0] += v[1]
        v[0] *= _R
        v[1] *= -1
        v[1] += a
        v[1] *= _R
    elif low == "x":
        _swap(v, 0, 1)
    elif low == "y":
        a = v[0].copy()
        v[0] = v[1]
        v[0] *= -1j
        v[1] = a
        v[1] *= 1j
    elif low in ("z", "s", "sdg", "t", "tdg", "phase"):
        k = op[2] if low == "phase" else {"z": 4, "s": 2, "sdg": 6, "t": 1, "tdg": 7}[low]
        v[1] *= _phase(k)
    elif low == "cx":
        _swap(v, (1, 0), (1, 1))
    elif low == "cz":
        v[1, 1] *= -1
    elif low == "swap":
        _swap(v, (0, 1), (1, 0))
    elif low == "ccx":
        _swap(v, (1, 1, 0), (1, 1, 1))
    elif low in ("ccz", "ccz_dg"):
        v[1, 1, 1] *= -1
    elif low == "cswap":
        _swap(v, (1, 0, 1), (1, 1, 0))
    else:
        raise ValueError(f"cannot simulate `{name}`")


def run(ops: list[tuple], state) -> None:
    for op in ops:
        apply_op(state, op)


def identity(n: int):
    return np.eye(2 ** n, dtype=complex).reshape([2] * n + [2 ** n])


def random_states(n: int, columns: int, seed: int):
    rng = np.random.default_rng(seed)
    psi = rng.normal(size=(2 ** n, columns)) + 1j * rng.normal(size=(2 ** n, columns))
    psi /= np.linalg.norm(psi, axis=0)
    return psi.reshape([2] * n + [columns])


def numeric_method(n: int, gates: int) -> str:
    """Which numeric check fits: ``unitary``, ``states`` or ``none``."""
    if np is None:
        return "none"
    if n <= UNITARY_MAX_QUBITS and gates * 4 ** n <= WORK_BUDGET:
        return "unitary"
    if n <= STATE_MAX_QUBITS and gates * 2 ** n <= WORK_BUDGET:
        return "states"
    return "none"


# Beyond the state-vector bound: a sparse simulation on a few random basis inputs.
# Toffoli-based circuits keep a basis state sparse (two terms inside a Toffoli), so
# this reaches any width; it gives up when the support passes the cap. Weaker than a
# random state: it samples sixteen columns of the operator, phases included, so a
# difference confined to a few inputs (a stray CCZ is seen on one input in eight)
# can be missed. A phase it reports is a witness; an `exact` is evidence.

SPARSE_SAMPLES = 16
SPARSE_CAP = 1 << 12
_SPARSE_PHASE = {"z": 4, "s": 2, "sdg": 6, "t": 1, "tdg": 7}


class SupportTooLarge(Exception):
    pass


def sparse_run(ops: list[tuple], n: int, x: int, cap: int = SPARSE_CAP) -> dict[int, complex]:
    """The state ``ops |x>`` as ``{basis index: amplitude}``; wire 0 is the top bit."""
    state = {x: 1 + 0j}
    w8 = [complex(np.exp(1j * np.pi * k / 4)) if np is not None else
          complex(*[(1, 0), (_R, _R), (0, 1), (-_R, _R), (-1, 0), (-_R, -_R), (0, -1),
                    (_R, -_R)][k]) for k in range(8)]
    bit = lambda w: 1 << (n - 1 - w)  # noqa: E731
    for op in ops:
        name, w = op[0].lower(), op[1]
        m = [bit(i) for i in w]
        if name == "h":
            new: dict[int, complex] = {}
            for k, amp in state.items():
                lo, a = k & ~m[0], amp * _R
                new[lo] = new.get(lo, 0) + a
                new[lo | m[0]] = new.get(lo | m[0], 0) + (-a if k & m[0] else a)
            state = {k: v for k, v in new.items() if abs(v) > 1e-12}
            if len(state) > cap:
                raise SupportTooLarge
        elif name == "x":
            state = {k ^ m[0]: v for k, v in state.items()}
        elif name == "y":
            state = {k ^ m[0]: v * (-1j if k & m[0] else 1j) for k, v in state.items()}
        elif name in _SPARSE_PHASE or name == "phase":
            f = w8[(op[2] if name == "phase" else _SPARSE_PHASE[name]) % 8]
            state = {k: v * f if k & m[0] else v for k, v in state.items()}
        elif name == "cx":
            state = {k ^ m[1] if k & m[0] else k: v for k, v in state.items()}
        elif name == "ccx":
            state = {k ^ m[2] if k & m[0] and k & m[1] else k: v for k, v in state.items()}
        elif name in ("cz", "ccz", "ccz_dg"):
            state = {k: -v if all(k & x for x in m) else v for k, v in state.items()}
        elif name in ("swap", "cswap"):
            a, b = m[-2], m[-1]
            on = (lambda k: True) if name == "swap" else (lambda k: k & m[0])
            state = {k ^ a ^ b if on(k) and bool(k & a) != bool(k & b) else k: v
                     for k, v in state.items()}
        else:
            raise ValueError(f"cannot simulate `{name}`")
    return state


def sparse_compare(a: list[tuple], b: list[tuple], n: int, seed: int = 1,
                   zero_wires: tuple = ()) -> dict:
    """``compare_lists`` on a few random basis inputs, at any width."""
    rng = random.Random(seed)
    method = f"sparse simulation on {SPARSE_SAMPLES} random basis inputs"
    powers = set()
    clear = sum(1 << (n - 1 - w) for w in zero_wires)
    for _ in range(SPARSE_SAMPLES):
        x = rng.getrandbits(n) & ~clear
        try:
            u, v = sparse_run(a, n, x), sparse_run(b, n, x)
        except SupportTooLarge:
            return {"relation": "unchecked", "method": "none (a basis input spreads over more "
                                                        f"than {SPARSE_CAP} basis states)"}
        if set(u) != set(v):
            return {"relation": "different", "method": method}
        k0 = max(u, key=lambda k: abs(u[k]))
        ratio = v[k0] / u[k0]
        turn = (np.angle(ratio) if np is not None else __import__("cmath").phase(ratio)) \
            / (3.141592653589793 / 4)
        if abs(abs(ratio) - 1) > 1e-9 or abs(turn - round(turn)) > 1e-7 or \
                any(abs(u[k] * ratio - v[k]) > 1e-9 for k in u):
            return {"relation": "different", "method": method}
        powers.add(int(round(turn)) % 8)
    if powers == {0}:
        return {"relation": "exact", "method": method}
    if len(powers) == 1:
        return {"relation": "phase", "omega_power": powers.pop(), "method": method}
    return {"relation": "different", "method": method}


def compare_lists(a: list[tuple], b: list[tuple], n: int, seed: int = 1,
                  zero_wires: tuple = ()) -> dict:
    """How two operation lists on ``n`` qubits relate: ``exact``, ``phase`` (``b`` is
    ``omega^k`` times ``a``, with ``k`` reported as ``omega_power``), ``different`` or
    ``unchecked``, and how that was found. With ``zero_wires`` the comparison is
    restricted to inputs in which those wires are ``|0>`` (clean ancillas)."""
    method = numeric_method(n, len(a) + len(b))
    if method == "none":
        return sparse_compare(a, b, n, seed, zero_wires)
    if method == "unitary":
        clear = sum(1 << (n - 1 - w) for w in zero_wires)
        keep = [c for c in range(2 ** n) if not c & clear]
        x = identity(n)[..., keep].copy()
        y = x.copy()
    else:
        cols = 2 if n <= 20 else 1
        x = random_states(n, cols, seed)
        for w in zero_wires:
            np.moveaxis(x, w, 0)[1] = 0
        x /= np.linalg.norm(x.reshape(2 ** n, -1), axis=0)
        y = x.copy()
    run(a, x)
    run(b, y)
    out = {"method": method if method == "unitary" else f"{x.shape[-1]} random state(s)"}
    gap = float(np.max(np.abs(x - y)))
    if gap < 1e-9:
        return {**out, "relation": "exact", "max_abs_diff": gap}
    x2, y2 = x.reshape(2 ** n, -1), y.reshape(2 ** n, -1)
    k = np.unravel_index(np.argmax(np.abs(x2)), x2.shape)
    ratio = y2[k] / x2[k]
    turn = np.angle(ratio) / (np.pi / 4)
    if abs(abs(ratio) - 1) < 1e-9 and abs(turn - round(turn)) < 1e-7 and \
            float(np.max(np.abs(x2 * ratio - y2))) < 1e-9:
        return {**out, "relation": "phase", "omega_power": int(round(turn)) % 8}
    return {**out, "relation": "different", "max_abs_diff": gap}


# --------------------------------------------------------------------------
# Counting and verification
# --------------------------------------------------------------------------

def counts(gates: list[Gate]) -> dict:
    names = [g[0] for g in gates]
    return {"gates": len(gates), "t_count": names.count("T") + names.count("Tdg"),
            "h_count": names.count("H"), "cx_count": names.count("CX")}


def fragment(gates: list[Gate]) -> str:
    used = {g[0] for g in gates}
    if used <= CLIFFORD:
        return "Clifford"
    if used <= CX_DIAGONAL:
        return "CX+diagonal"
    return "general"


def tier(qubits: int, gates: int) -> int:
    for k, (q, g) in enumerate(TIERS):
        if qubits <= q and gates <= g:
            return k + 1
    return len(TIERS) + 1


_EXPANSION = {"cz": 3, "swap": 3, "ccx": 15, "ccz": 13, "ccz_dg": 13, "cswap": 17}
_T_PER_OP = {"ccx": 7, "ccz": 7, "ccz_dg": 7, "cswap": 7, "t": 1, "tdg": 1}


def bookkeeping(ops: list[tuple], gates: list[Gate], n: int) -> None:
    """The structural invariants every translation must satisfy at any width."""
    want = sum(_EXPANSION.get(o[0], len(PHASES[o[2] % 8]) if o[0] == "phase" else 1)
               for o in ops)
    want_t = sum(_T_PER_OP.get(o[0], 1 if o[0] == "phase" and o[2] % 2 else 0) for o in ops)
    have = counts(gates)
    if have["gates"] != want or have["t_count"] != want_t:
        raise AssertionError(f"gate bookkeeping: {have} against {want} gates, {want_t} T")
    for name, w in gates:
        if name not in ALPHABET or any(not 0 <= i < n for i in w) or len(set(w)) != len(w) \
                or len(w) != (2 if name == "CX" else 1):
            raise AssertionError(f"not a gate of the alphabet on {n} wires: {name} {w}")


def verify(ops: list[tuple], gates: list[Gate], n: int) -> dict:
    """Check a translation against its native operations, global phase included."""
    bookkeeping(ops, gates, n)
    if all(o[0] in ONE_QUBIT or o[0] == "cx" for o in ops):
        # nothing was expanded, so there is nothing for a simulation to compare
        return {"method": "identity translation", "numeric": False}
    t0 = time.time()
    res = compare_lists(ops, gates, n)
    if res["relation"] == "unchecked":
        return {"method": "gate bookkeeping only", "numeric": False, "why": res["method"]}
    if res["relation"] != "exact":
        raise AssertionError(f"the translation is not exact: {res}")
    return {"method": res["method"], "numeric": True,
            **({"max_abs_diff": res["max_abs_diff"]} if "max_abs_diff" in res else {}),
            "seconds": round(time.time() - t0, 2)}


# --------------------------------------------------------------------------
# Fetch
# --------------------------------------------------------------------------

def raw_url(source: str, path: str) -> str:
    s = SOURCES[source]
    owner_repo = s["url"].split("github.com/")[1]
    return (f"https://raw.githubusercontent.com/{owner_repo}/{s['commit']}/"
            + urllib.parse.quote(path))


def cached_path(source: str, path: str) -> Path:
    return cache_dir() / "files" / source / SOURCES[source]["commit"] / path


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def download(url: str, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    tmp = dst.with_name(dst.name + ".part")
    if shutil.which("curl"):
        subprocess.run(["curl", "-sS", "-L", "--fail", "--max-time", "300", "-o", str(tmp), url],
                       check=True)
    else:
        with urllib.request.urlopen(url, timeout=300) as r, tmp.open("wb") as f:
            shutil.copyfileobj(r, f)
    tmp.replace(dst)


def load_manifest() -> dict:
    return json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}


def recorded_hashes(manifest: dict) -> dict[tuple[str, str], str]:
    out = {}
    for rec in manifest.get("circuits", []) + manifest.get("published", []):
        if rec.get("path") and rec.get("sha256"):
            out[(rec["source"], rec["path"])] = rec["sha256"]
    for name, s in manifest.get("sources", {}).items():
        if s.get("licence_path") and s.get("licence_sha256"):
            out[(name, s["licence_path"])] = s["licence_sha256"]
    return out


def fetch_file(source: str, path: str, hashes: dict, quiet: bool = False) -> Path:
    """The cached copy of a source file, downloaded if missing, hash-checked if known."""
    dst = cached_path(source, path)
    if not dst.exists():
        download(raw_url(source, path), dst)
        if not quiet:
            print(f"fetched {source}:{path} ({dst.stat().st_size} bytes)")
    want = hashes.get((source, path))
    if want and sha256(dst) != want:
        raise RuntimeError(f"{source}:{path}: sha256 differs from the manifest; delete {dst} "
                           "to fetch it again, or the source has changed")
    return dst


# --------------------------------------------------------------------------
# Building a record
# --------------------------------------------------------------------------

def load_ops(spec: dict, hashes: dict) -> tuple[dict, dict]:
    """Parse a spec's source (fetching it if needed): the parse and its provenance."""
    if spec["format"] == "generator":
        family = spec["family"].removeprefix("gen_")
        n, ops, layout = GENERATORS[family](spec["size"])
        return ({"qubits": n, "ops": ops, "dropped": {}, "uses_rz": False, "notes": [layout]},
                {"generator": f"scripts/circuit_sources.py gen_{family}({spec['size']})"})
    path = fetch_file(spec["source"], spec["path"], hashes, quiet=True)
    parsed = PARSERS[spec["format"]](path.read_text())
    s = SOURCES[spec["source"]]
    return parsed, {"url": s["url"], "commit": s["commit"], "path": spec["path"],
                    "sha256": sha256(path), "bytes": path.stat().st_size,
                    "licence": s["licence"]}


def tzap_cross_check(spec: dict, gates: list[Gate], n: int, hashes: dict) -> str | None:
    """Compare a Feynman translation with TZAP's own pre-decomposed copy, gate by gate."""
    if spec["source"] != "feynman" or spec["name"] == "feynman_qft_4":
        return None
    path = "benchmarks/feynman/" + Path(spec["path"]).name
    theirs = parse_qasm(fetch_file("tzap", path, hashes, quiet=True).read_text())
    if theirs["qubits"] != n or translate(theirs["ops"]) != gates:
        raise AssertionError(f"{spec['name']}: differs from TZAP's pre-decomposed copy")
    return f"identical, gate by gate, to tzap:{path}"


PYZX_CHECK_MAX_BYTES = 2_000_000


def pyzx_cross_check(spec: dict, path: Path, strings: list[str], n: int) -> str | None:
    """An independent reader of the same file: PyZX's QASM parser and its own Toffoli
    decomposition, compared with this translation (gate lists, else numerically)."""
    if spec["format"] != "qasm2" or path.stat().st_size > PYZX_CHECK_MAX_BYTES:
        return None
    try:
        import pyzx as zx
        import check_pyzx_benchmarks as cpb
    except ImportError:
        return None
    text = re.sub(r"//[^\n]*", "", path.read_text())
    text = re.sub(r"\b(measure|creg)\b[^;]*;", "", text)
    if "OPENQASM" not in text:
        text = "OPENQASM 2.0;\n" + text
    try:
        theirs = cpb.lean_instructions(zx.Circuit.from_qasm(text.strip()).to_basic_gates())
    except Exception as e:  # noqa: BLE001 (PyZX raises several types)
        return f"PyZX's parser does not apply ({type(e).__name__}: {str(e)[:80]})"
    if theirs == strings:
        return "PyZX's parser gives the same gate list"
    res = compare_lists(parse_gates(theirs), parse_gates(strings), n)
    if res["relation"] == "exact":
        return f"PyZX's parser and decomposition give the same operator ({res['method']})"
    if res["relation"] == "unchecked":
        return "PyZX's gate list differs and the register is too wide to compare numerically"
    raise AssertionError(f"{spec['name']}: PyZX reads this file differently: {res}")


def gates_digest(n: int, strings: list[str]) -> str:
    return hashlib.sha256((str(n) + "\n" + "\n".join(strings)).encode()).hexdigest()


def build(spec: dict, hashes: dict, check: bool = True, cross: bool = True) -> tuple[dict, list]:
    """The manifest record of one circuit and its gate strings."""
    parsed, provenance = load_ops(spec, hashes)
    n = parsed["qubits"]
    gates = translate(parsed["ops"])
    strings = [show(g) for g in gates]
    rec = {"name": spec["name"], "family": spec["family"], "size": spec["size"],
           "source": spec["source"], "path": spec["path"], "format": spec["format"],
           **{k: provenance[k] for k in ("sha256", "bytes") if k in provenance},
           "qubits": n, **counts(gates), "fragment": fragment(gates),
           "tier": tier(n, len(gates)),
           "native_ops": {k: sum(o[0] == k for o in parsed["ops"])
                          for k in sorted({o[0] for o in parsed["ops"]})},
           "dropped": parsed["dropped"],
           "rz_convention": ("rz present: read as diag(1, exp(i*theta)) (qelib1.inc and PyZX); "
                             "Qiskit's rz differs by exp(-i*theta/2)") if parsed["uses_rz"]
           else "u1/p only: diag(1, exp(i*theta)) in every convention"
           if parsed.get("phase_gates") else "no rz, u1 or p gate in the file"
           if spec["format"] == "qasm2" else "n/a",
           "notes": parsed["notes"] + ([spec["note"]] if spec.get("note") else []),
           "translated_sha256": gates_digest(n, strings)}
    if check:
        rec["verified"] = verify(parsed["ops"], gates, n)
        if cross and tier(n, len(gates)) <= 3 or cross and cached_tzap(spec):
            note = tzap_cross_check(spec, gates, n, hashes)
            if note:
                rec["verified"]["cross_check"] = note
        if cross and spec["path"]:
            note = pyzx_cross_check(spec, cached_path(spec["source"], spec["path"]), strings, n)
            if note:
                rec["verified"]["pyzx_parser"] = note
    return rec, strings


def cached_tzap(spec: dict) -> bool:
    """Whether TZAP's copy of a large Feynman file is already in the cache."""
    return spec["source"] == "feynman" and \
        cached_path("tzap", "benchmarks/feynman/" + Path(spec["path"]).name).exists()


def circuit_json(rec: dict, strings: list[str]) -> dict:
    s = SOURCES[rec["source"]]
    return {"name": rec["name"], "qubits": rec["qubits"], "gates": strings,
            "family": rec["family"], "size": rec["size"],
            "source": {"source": rec["source"], "url": s["url"], "commit": s["commit"],
                       "path": rec["path"], "sha256": rec.get("sha256"),
                       "licence": s["licence"]},
            "counts": {k: rec[k] for k in ("gates", "t_count", "h_count", "cx_count")},
            "fragment": rec["fragment"], "tier": rec["tier"], "dropped": rec["dropped"],
            "verified": rec.get("verified"), "translated_sha256": rec["translated_sha256"]}


def to_qasm(name: str, n: int, strings: list[str]) -> str:
    """The translated circuit as OpenQASM 2.0 in the alphabet's own gates, for tools that
    read QASM (TZAP, PyZX, Feynman). No `rz`: the convention question does not arise."""
    lines = ["OPENQASM 2.0;", 'include "qelib1.inc";',
             f"// {name}: written by scripts/circuit_sources.py translate --qasm", f"qreg q[{n}];"]
    for g in strings:
        gate, *wires = g.split()
        lines.append(f"{gate.lower()} " + ",".join(f"q[{w}]" for w in wires) + ";")
    return "\n".join(lines) + "\n"


def load_circuit(name: str, check: bool = False) -> dict:
    """Name -> the per-circuit JSON (fetching and translating as needed)."""
    rec, strings = build(find_spec(name), recorded_hashes(load_manifest()), check=check,
                         cross=False)
    return circuit_json(rec, strings)


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------

def cmd_fetch(args) -> None:
    hashes = recorded_hashes(load_manifest())
    manifest_tiers = {r["name"]: r["tier"] for r in load_manifest().get("circuits", [])}
    wanted = [find_spec(n) for n in args.names] if args.names else \
        circuit_specs() + (published_specs() if args.published or args.all else [])
    got = 0
    for name, s in SOURCES.items():
        if s["licence_path"]:
            fetch_file(name, s["licence_path"], hashes)
    for spec in wanted:
        if spec["format"] == "generator":
            continue
        if not (args.all or args.names) and manifest_tiers.get(spec["name"], 1) > 3:
            continue
        fetch_file(spec["source"], spec["path"], hashes)
        if spec["source"] == "feynman" and spec["name"] != "feynman_qft_4":
            fetch_file("tzap", "benchmarks/feynman/" + Path(spec["path"]).name, hashes)
        got += 1
    print(f"{got} circuit files present under {cache_dir() / 'files'}")


def cmd_translate(args) -> None:
    hashes = recorded_hashes(load_manifest())
    out = args.out or cache_dir() / "circuits"
    out.mkdir(parents=True, exist_ok=True)
    names = args.names or [s["name"] for s in circuit_specs()
                           if load_tier(s["name"]) <= (4 if args.all else 3)]
    for name in names:
        try:
            rec, strings = build(find_spec(name), hashes, check=not args.no_verify)
        except Rejected as e:
            print(f"{name}: REJECTED: {e}")
            continue
        (out / f"{name}.json").write_text(json.dumps(circuit_json(rec, strings)) + "\n")
        if args.qasm:
            (out / f"{name}.qasm").write_text(to_qasm(name, rec["qubits"], strings))
        print(f"{name}: {rec['qubits']} qubits, {rec['gates']} gates, T {rec['t_count']}, "
              f"{rec['fragment']}, tier {rec['tier']}, "
              f"{rec.get('verified', {}).get('method', 'not verified')}")


def load_tier(name: str) -> int:
    for r in load_manifest().get("circuits", []):
        if r["name"] == name:
            return r["tier"]
    return 1


def cmd_catalogue(args) -> None:
    if args.table or args.readme:
        if args.readme:
            replace_block(CATALOGUE / "README.md", "LADDER", markdown_table(load_manifest()))
        else:
            print(markdown_table(load_manifest()))
        return
    old = load_manifest()
    hashes = recorded_hashes(old) if not args.rehash else {}
    circuits, published, rejected = [], [], []
    specs = [(s, circuits) for s in circuit_specs()] + \
            [(s, published) for s in published_specs()]
    for spec, bucket in specs:
        if args.only and not any(spec["name"].startswith(p) for p in args.only):
            kept = [r for r in old.get("circuits", []) + old.get("published", [])
                    if r["name"] == spec["name"]]
            bucket += kept
            continue
        t0 = time.time()
        try:
            rec, _ = build(spec, hashes)
        except Rejected as e:
            rejected.append({"source": spec["source"], "path": spec["path"], "by": "parser",
                             "reason": str(e)})
            print(f"{spec['name']}: REJECTED: {e}", flush=True)
            continue
        except subprocess.CalledProcessError:
            rejected.append({"source": spec["source"], "path": spec["path"], "by": "fetch",
                             "reason": "not present at the pinned commit"})
            print(f"{spec['name']}: not present at the pinned commit", flush=True)
            continue
        bucket.append(rec)
        print(f"{rec['name']}: {rec['qubits']}q {rec['gates']}g T{rec['t_count']} tier "
              f"{rec['tier']} [{rec['verified']['method']}] {time.time() - t0:.1f}s", flush=True)
    if args.only:
        redone = {s["path"] for s, _ in specs if any(s["name"].startswith(p) for p in args.only)}
        rejected += [r for r in old.get("rejected", [])
                     if r.get("by") != "survey" and r["path"] not in redone]
    rejected += [{"source": s, "path": p, "by": "survey", "reason": why}
                 for s, p, why in SURVEY_REJECTED]
    sources = {}
    for name, s in SOURCES.items():
        sources[name] = dict(s)
        if s["licence_path"]:
            sources[name]["licence_sha256"] = sha256(fetch_file(name, s["licence_path"], hashes))
    manifest = {
        "schema": 1,
        "generated_by": "scripts/circuit_sources.py catalogue --write",
        "alphabet": list(ALPHABET),
        "tiers": [{"tier": k + 1, "max_qubits": q, "max_gates": g}
                  for k, (q, g) in enumerate(TIERS)] + [{"tier": 4, "beyond": True}],
        "translation": {
            "cz a b": "H b; CX a b; H b", "swap a b": "CX a b; CX b a; CX a b",
            "ccx a b c": [show(g) for g in ccx_gates(0, 1, 2)],
            "ccz a b c": [show(g) for g in ccz_gates(0, 1, 2)],
            "Zd a b c (.qc)": "the ccz list reversed with every gate inverted",
            "cswap a b c": "CX c b; ccx a b c; CX c b",
            "u1/p/rz(k*pi/4)": {str(k): v for k, v in PHASES.items()},
            "dropped without changing the unitary": "barrier, id, terminal measure",
        },
        "sources": sources, "circuits": circuits, "published": published, "rejected": rejected,
    }
    if args.write:
        CATALOGUE.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")
        print(f"wrote {MANIFEST.relative_to(ROOT)}: {len(circuits)} circuits, "
              f"{len(published)} published files, {len(rejected)} rejections")


def replace_block(path: Path, name: str, text: str) -> None:
    """Replace what stands between `<!-- BEGIN name -->` and `<!-- END name -->` in a file."""
    begin, end = f"<!-- BEGIN {name} -->", f"<!-- END {name} -->"
    doc = path.read_text()
    if doc.count(begin) != 1 or doc.count(end) != 1:
        raise SystemExit(f"{path}: expected one `{begin}` and one `{end}`")
    head, rest = doc.split(begin)
    path.write_text(head + begin + "\n" + text.rstrip("\n") + "\n" + end + rest.split(end)[1])


def markdown_table(manifest: dict) -> str:
    """The ladder as Markdown, one table per tier."""
    out = []
    for t in (1, 2, 3, 4):
        rows = [r for r in manifest.get("circuits", []) if r["tier"] == t]
        rows.sort(key=lambda r: (r["qubits"] * 0 + r["gates"], r["qubits"], r["name"]))
        out += [f"### Tier {t}", "",
                "| Name | Family | Size | Qubits | Gates | T | H | CX | Fragment | Source | "
                "Verified |", "|---|---|---:|---:|---:|---:|---:|---:|---|---|---|"]
        for r in rows:
            v = r["verified"]
            how = v["method"] + ("; = TZAP copy" if v.get("cross_check") else "") + \
                ("; PyZX parser agrees" if v.get("pyzx_parser", "").startswith("PyZX's parser ")
                 and "does not apply" not in v["pyzx_parser"] else "")
            out.append(f"| `{r['name']}` | {r['family']} | {r['size']} | {r['qubits']} | "
                       f"{r['gates']} | {r['t_count']} | {r['h_count']} | {r['cx_count']} | "
                       f"{r['fragment']} | {r['source']} | {how} |")
        out.append("")
    return "\n".join(out)


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------

def self_test() -> None:
    """The translation rules, the parsers, the generators and the simulator."""
    if np is None:
        raise SystemExit("the self-test needs numpy")

    def unitary(ops, n):
        u = identity(n)
        run(ops, u)
        return u.reshape(2 ** n, 2 ** n)

    # 1. the simulator against explicit matrices (qubit 0 most significant)
    w8 = np.exp(1j * np.pi / 4)
    mats = {"h": np.array([[1, 1], [1, -1]]) / np.sqrt(2), "x": np.array([[0, 1], [1, 0]]),
            "y": np.array([[0, -1j], [1j, 0]]), "z": np.diag([1, -1]), "s": np.diag([1, 1j]),
            "sdg": np.diag([1, -1j]), "t": np.diag([1, w8]), "tdg": np.diag([1, 1 / w8])}
    for name, m in mats.items():
        assert np.allclose(unitary([(name, (0,))], 1), m), name
        assert np.allclose(unitary([(name, (1,))], 2), np.kron(np.eye(2), m)), name
        assert np.allclose(unitary([(ONE_QUBIT[name], (0,))], 2), np.kron(m, np.eye(2))), name
    for k in range(8):
        assert np.allclose(unitary([("phase", (0,), k)], 1), np.diag([1, w8 ** k]))

    def perm(n, f):
        m = np.zeros((2 ** n, 2 ** n))
        for x in range(2 ** n):
            bits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
            y = sum(b << (n - 1 - i) for i, b in enumerate(f(bits)))
            m[y, x] = 1
        return m

    assert np.allclose(unitary([("cx", (0, 1))], 2), perm(2, lambda b: [b[0], b[0] ^ b[1]]))
    assert np.allclose(unitary([("cx", (1, 0))], 2), perm(2, lambda b: [b[0] ^ b[1], b[1]]))
    assert np.allclose(unitary([("swap", (0, 1))], 2), perm(2, lambda b: [b[1], b[0]]))
    assert np.allclose(unitary([("ccx", (0, 1, 2))], 3),
                       perm(3, lambda b: [b[0], b[1], b[2] ^ (b[0] & b[1])]))
    assert np.allclose(unitary([("cswap", (0, 1, 2))], 3),
                       perm(3, lambda b: [b[0]] + ([b[2], b[1]] if b[0] else [b[1], b[2]])))
    assert np.allclose(unitary([("cz", (0, 1))], 2), np.diag([1, 1, 1, -1]))
    assert np.allclose(unitary([("ccz", (0, 1, 2))], 3), np.diag([1] * 7 + [-1]))

    # 2. every translation rule on every wire assignment of four wires, phase included
    from itertools import permutations
    for name, arity in NATIVE_ARITY.items():
        for w in permutations(range(4), arity):
            ops = [("phase", w, k) for k in range(8)] if name == "phase" else [(name, w)]
            for op in ops:
                res = compare_lists([op], translate_op(op), 4)
                assert res["relation"] == "exact", (op, res)
    res = compare_lists([("t", (0,))], [("s", (0,))], 1)
    assert res["relation"] == "different"
    res = compare_lists([("x", (0,)), ("z", (0,)), ("x", (0,)), ("z", (0,))], [], 1)
    assert res == {"method": "unitary", "relation": "phase", "omega_power": 4}, res
    res = compare_lists([("h", (0,)), ("t", (11,))], [("t", (11,)), ("h", (0,))], 12)
    assert res["relation"] == "exact" and res["method"] == "2 random state(s)", res
    # S X S X = i, so the empty circuit is omega^6 times it
    res = compare_lists([("s", (3,)), ("x", (3,)), ("s", (3,)), ("x", (3,))], [], 12)
    assert res["relation"] == "phase" and res["omega_power"] == 6, res

    # 2b. the sparse simulator against the dense one, and its three verdicts
    rng = random.Random(5)
    names = list(NATIVE_ARITY)
    for _ in range(30):
        ops = []
        for _ in range(25):
            name = rng.choice(names)
            w = tuple(rng.sample(range(5), NATIVE_ARITY[name]))
            ops.append(("phase", w, rng.randrange(8)) if name == "phase" else (name, w))
        x = rng.getrandbits(5)
        dense = identity(5)
        run(ops, dense)
        col = dense.reshape(32, 32)[:, x]
        got = sparse_run(ops, 5, x)
        assert all(abs(col[k] - got.get(k, 0)) < 1e-9 for k in range(32)), ops
    wide = translate(gen_cuccaro(40)[1])
    assert sparse_compare(gen_cuccaro(40)[1], wide, 82)["relation"] == "exact"
    assert sparse_compare(wide, wide[:-1], 82)["relation"] == "different"
    res = sparse_compare(wide, wide + [("X", (0,)), ("Z", (0,)), ("X", (0,)), ("Z", (0,))], 82)
    assert res["relation"] == "phase" and res["omega_power"] == 4, res
    assert sparse_compare([("h", (i,)) for i in range(40)], [], 40)["relation"] == "unchecked"
    assert compare_lists(gen_cuccaro(40)[1], wide, 82)["method"].startswith("sparse")
    # restricted to clean ancillas: X on a control-0 wire is invisible only there
    for n_, extra in ((3, []), (12, [("h", (9,)), ("h", (9,))]), (30, [])):
        a_, b_ = [("cx", (0, 1))] + extra, [("cx", (0, 1)), ("cz", (1, 2))] + extra
        assert compare_lists(a_, b_, n_)["relation"] == "different", n_
        assert compare_lists(a_, b_, n_, zero_wires=(2,))["relation"] == "exact", n_
        assert compare_lists(a_, b_, n_, zero_wires=(1,))["relation"] == "different", n_

    # 3. the QASM reader: registers, broadcast, gate definitions, angles, refusals
    text = """OPENQASM 2.0; include "qelib1.inc";
    gate majority a,b,c { cx c,b; cx c,a; ccx a,b,c; }
    gate ph(theta) q { u1(theta/2) q; rz(-theta/2 + pi) q; }
    qreg cin[1]; qreg a[2]; qreg b[2]; creg ans[2];
    x b; // broadcast
    majority cin[0],b[0],a[0]; barrier a; id a[1];
    ph(pi/2) a[1]; u1(0) a[0]; cz a, b;
    measure b -> ans;"""
    p = parse_qasm(text)
    assert p["qubits"] == 5 and p["uses_rz"] and p["dropped"] == {"barrier": 1, "id": 1,
                                                                  "measure": 2}
    assert p["phase_gates"] == ["rz", "u1"]
    assert p["ops"] == [("x", (3,)), ("x", (4,)), ("cx", (1, 3)), ("cx", (1, 0)),
                        ("ccx", (0, 3, 1)), ("phase", (2,), 1), ("phase", (2,), 3),
                        ("cz", (1, 3)), ("cz", (2, 4))], p["ops"]
    gates = translate(p["ops"])
    assert verify(p["ops"], gates, 5)["method"] == "unitary"
    assert [show(g) for g in gates[-6:]] == ["H 3", "CX 1 3", "H 3", "H 4", "CX 2 4", "H 4"]
    refusals = {
        "qreg q[2]; rz(pi/8) q[0];": "not a multiple of pi/4",
        "qreg q[2]; rz(0.785398) q[0];": "not a multiple of pi/4",
        "qreg q[2]; creg c[2]; measure q[0] -> c[0]; h q[0];": "after it was measured",
        "qreg q[2]; creg c[2]; if(c==1) x q[0];": "classical control",
        "qreg q[2]; reset q[0];": "reset",
        "qreg q[2]; u3(pi/2,0,pi) q[0];": "outside the alphabet",
        "qreg q[2]; cx q[0],q[0];": "repeated wire",
        "qreg q[2]; h q[2];": "off its register",
        "OPENQASM 3.0; qubit[2] q;": "only OpenQASM 2.0",
    }
    for src, why in refusals.items():
        try:
            parse_qasm(src)
        except Rejected as e:
            assert why in str(e), (src, str(e))
        else:
            raise AssertionError(f"accepted: {src}")
    # a measurement whose qubit is never touched again is terminal
    ok = parse_qasm("qreg q[2]; creg c[2]; h q[0]; measure q[0] -> c[0]; h q[1];")
    assert ok["ops"] == [("h", (0,)), ("h", (1,))] and ok["dropped"] == {"measure": 1}

    back = parse_qasm(to_qasm("t", 5, [show(g) for g in gates]))
    assert back["qubits"] == 5 and translate(back["ops"]) == gates

    # 4. the .qc and Quipper readers
    qc = parse_qc(".v b c a\n.i b c\nBEGIN\nH a\nZ b c a\nZd b c a\ntof b a\ntof a\nT* c\n"
                  "P b\ncnot c b\nEND\n")
    assert qc["qubits"] == 3 and qc["ops"] == [
        ("h", (2,)), ("ccz", (0, 1, 2)), ("ccz_dg", (0, 1, 2)), ("cx", (0, 2)), ("x", (2,)),
        ("tdg", (1,)), ("s", (0,)), ("cx", (1, 0))] and "not primary inputs" in qc["notes"][0]
    assert verify(qc["ops"], translate(qc["ops"]), 3)["numeric"]
    try:
        parse_qc(".v a b c d\nBEGIN\ntof a b c d\nEND\n")
    except Rejected as e:
        assert "ancilla" in str(e)
    else:
        raise AssertionError("a three-control Toffoli was accepted")
    qp = parse_quipper('Inputs: 0:Qbit, 1:Qbit, 2:Qbit\nQGate["H"](2) with nocontrol\n'
                       'QGate["Z"](2) with controls=[+0,-1] with nocontrol\n'
                       'QGate["not"](1) with controls=[+2] with nocontrol\n'
                       'QGate["T"]*(0) with nocontrol\nOutputs: 0:Qbit, 1:Qbit, 2:Qbit\n')
    assert qp["ops"] == [("h", (2,)), ("x", (1,)), ("ccz", (0, 1, 2)), ("x", (1,)),
                         ("cx", (2, 1)), ("tdg", (0,))], qp["ops"]
    try:
        parse_quipper('Inputs: 0:Qbit\nQRot["exp(-i%Z)",0.39](0) with nocontrol\n')
    except Rejected as e:
        assert "not a plain gate" in str(e)
    else:
        raise AssertionError("a rotation was accepted")

    # 5. the generators against their specifications, as classical functions
    def classical(ops, bits):
        bits = list(bits)
        for name, w in ops:
            if name == "cx":
                bits[w[1]] ^= bits[w[0]]
            elif name == "ccx":
                bits[w[2]] ^= bits[w[0]] & bits[w[1]]
            else:
                raise AssertionError(name)
        return bits

    rng = random.Random(7)
    for k in (3, 4, 9, 40):
        for gen, clean in ((gen_tof, True), (gen_barenco_tof, False)):
            n, ops, _ = gen(k)
            for _ in range(50):
                bits = [rng.randrange(2) for _ in range(n)]
                if rng.random() < 0.5:
                    bits[:k] = [1] * k
                if clean:
                    bits[k:2 * k - 2] = [0] * (k - 2)
                want = list(bits)
                want[-1] ^= int(all(bits[:k]))
                assert classical(ops, bits) == want, (gen.__name__, k)
    for k in (1, 2, 5, 33):
        n, ops, _ = gen_cuccaro(k)
        for _ in range(50):
            bits = [rng.randrange(2) for _ in range(n)]
            a = sum(bits[2 + 2 * i] << i for i in range(k))
            b = sum(bits[1 + 2 * i] << i for i in range(k))
            total = a + b + bits[0]
            want = list(bits)
            for i in range(k):
                want[1 + 2 * i] = (total >> i) & 1
            want[-1] ^= (total >> k) & 1
            assert classical(ops, bits) == want, ("cuccaro", k)
    n, ops, _ = gen_ghz(6)
    psi = np.zeros(2 ** n, dtype=complex)
    psi[0] = 1
    psi = psi.reshape([2] * n + [1])
    run(translate(ops), psi)
    flat = psi.reshape(-1)
    assert abs(flat[0] - _R) < 1e-12 and abs(flat[-1] - _R) < 1e-12
    n, ops, _ = gen_surface(3)
    assert n == 17 and fragment(translate(ops)) == "Clifford"
    # two identical rounds of CSS syndrome extraction undo each other
    assert compare_lists(ops, [], n)["relation"] == "exact"
    for family, size in GENERATED[:3] + [("cuccaro", 4)]:
        n, ops, _ = GENERATORS[family](size)
        assert verify(ops, translate(ops), n)["numeric"]
    assert verify(ops_s := gen_surface(3)[1], translate(ops_s), 17) == {
        "method": "identity translation", "numeric": False}

    # 6. against the repository's own generators, when pyzx is importable
    try:
        import tcount_survey as ts
    except ImportError:
        print("(pyzx not importable: skipped the comparison with tcount_survey.py)")
    else:
        for k in (3, 4, 5):
            assert translate(gen_tof(k)[1]) == ts.tof(k)[1]
            assert translate(gen_barenco_tof(k)[1]) == ts.barenco_tof(k)[1]
            assert translate(gen_cuccaro(k)[1]) == ts.cuccaro(k)[1]
        assert ccx_gates(0, 1, 2) == ts.ccx(0, 1, 2) and ccz_gates(0, 1, 2) == ts.ccz(0, 1, 2)
        g = translate(gen_cuccaro(2)[1])
        u = identity(6)
        run(g, u)
        assert np.allclose(u.reshape(64, 64), ts.unitary(g, 6))
    assert tier(10, 200) == 1 and tier(11, 10) == 2 and tier(30, 2001) == 3 and tier(101, 1) == 4
    print("self-test passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--self-test", action="store_true")
    sub = parser.add_subparsers(dest="command")
    p = sub.add_parser("fetch", help="download the source files into the cache")
    p.add_argument("names", nargs="*")
    p.add_argument("--all", action="store_true", help="also tier 4 and the published outputs")
    p.add_argument("--published", action="store_true", help="also the published outputs")
    p = sub.add_parser("translate", help="write one JSON per circuit")
    p.add_argument("names", nargs="*")
    p.add_argument("--out", type=Path)
    p.add_argument("--all", action="store_true", help="also tier 4")
    p.add_argument("--no-verify", action="store_true")
    p.add_argument("--qasm", action="store_true", help="also write NAME.qasm in the alphabet")
    p = sub.add_parser("catalogue", help="recompute the manifest")
    p.add_argument("--write", action="store_true")
    p.add_argument("--table", action="store_true", help="print the manifest as Markdown")
    p.add_argument("--readme", action="store_true",
                   help="put that table between the LADDER markers of the catalogue's README")
    p.add_argument("--only", nargs="*", help="name prefixes to recompute; keep the rest")
    p.add_argument("--rehash", action="store_true", help="ignore the recorded sha256 values")
    args = parser.parse_args()
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    if args.self_test:
        self_test()
    elif args.command == "fetch":
        cmd_fetch(args)
    elif args.command == "translate":
        cmd_translate(args)
    elif args.command == "catalogue":
        cmd_catalogue(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
