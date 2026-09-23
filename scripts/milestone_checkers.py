#!/usr/bin/env python3
"""Measure installed checkers on saved milestone pairs, sequentially and resumably.

The worker reuses hard_pair.py for the existing checker configurations. QuiZX
also gets a closed-miter stabilizer-decomposition check: for unitary U and V,
|tr(V†U)|² = 4^n iff they agree up to global phase. Scalar.is_one performs the
library's scalar equality check; no floating-point tolerance is used here.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time
from importlib import metadata

import hard_pair

CHECKERS = ('qcec', 'qcec_dd', 'pyzx', 'quizx', 'quizx_decompose')
RUNS = {1: '20260922-223918-2db1eb', 3: '20260922-225611-73c7d3'}


def quizx_decompose(a: Path, b: Path) -> dict:
    import quizx
    n, _ = hard_pair.parse_qasm(a.read_text())
    text_a, text_b = a.read_text(), b.read_text()
    body = [line for line in text_b.splitlines()
            if line and line.split()[0] in hard_pair.QASM_INVERSE]
    inv = [hard_pair.QASM_INVERSE[line.split()[0]] + line[len(line.split()[0]):]
           for line in reversed(body)]
    g = quizx.qasm(text_a + '\n'.join(inv) + '\n')
    ins, outs = list(g.inputs()), list(g.outputs())
    if len(ins) != n or len(outs) != n:
        raise ValueError('QuiZX did not retain the complete input/output register')
    # A degree-two zero-phase Z spider is an identity wire. Connect each
    # output back to the matching input, closing the diagram into its trace.
    for i, o in zip(ins, outs):
        g.set_type(i, 1)
        g.set_type(o, 1)
        v = g.add_vertex(ty=1)
        g.add_edge((i, v))
        g.add_edge((v, o))
    g.set_inputs([])
    g.set_outputs([])
    quizx.full_simp(g)
    remaining = g.num_vertices()
    d = quizx.Decomposer(g, simp=quizx.SimpFunc.FullSimp)
    d.decompose(driver_type='BssWithCats', random_t=False)
    scalar = d.get_scalar()
    norm = scalar * scalar.conjugate() * quizx.Scalar.sqrt2_pow(-4 * n)
    return {'verdict': 'equivalent' if norm.is_one() else 'not_equivalent',
            'method': 'full_simp then BssWithCats on the closed miter trace',
            'vertices_after_full_simp': remaining,
            'decomposition_terms': d.get_nterms(),
            'normalized_trace_norm_squared': norm.to_json()}


def rss_tree(root: int) -> int:
    p = subprocess.run(['ps', '-axo', 'pid=,ppid=,rss='], capture_output=True, text=True,
                       check=True)
    entries = [tuple(map(int, line.split())) for line in p.stdout.splitlines()]
    ids = {root}
    while True:
        enlarged = ids | {pid for pid, parent, _ in entries if parent in ids}
        if enlarged == ids:
            break
        ids = enlarged
    return sum(rss for pid, _, rss in entries if pid in ids)


def measured(checker: str, a: Path, b: Path, folder: Path, seconds: float,
             memory_gib: float) -> dict:
    folder.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, str(Path(__file__).resolve()), 'worker', checker,
               a.name, b.name, '--seconds', str(seconds)]
    (folder / 'command.json').write_text(json.dumps({'argv': command, 'cwd': str(a.parent)},
                                                  indent=2))
    start = time.time()
    peak = 0
    verdict = None
    with (folder / 'stdout.log').open('w') as stdout, (folder / 'stderr.log').open('w') as stderr:
        proc = subprocess.Popen(command, cwd=a.parent, stdout=stdout, stderr=stderr,
                                stdin=subprocess.DEVNULL, start_new_session=True)
        try:
            while proc.poll() is None:
                peak = max(peak, rss_tree(proc.pid))
                if peak > memory_gib * 2**20:
                    verdict = 'memory_limit'
                elif time.time() - start >= seconds:
                    verdict = 'timeout'
                if verdict:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                    break
                time.sleep(0.25)
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
    result = {'checker': checker, 'wall_seconds': round(time.time() - start, 3),
              'peak_rss_gib': round(peak / 2**20, 4), 'returncode': proc.returncode,
              'time_limit_seconds': seconds, 'memory_limit_gib': memory_gib,
              'logs': str(folder)}
    if verdict:
        result['verdict'] = verdict
    else:
        try:
            parsed = json.loads((folder / 'stdout.log').read_text().strip().splitlines()[-1])
            if proc.returncode != 0:
                raise ValueError('nonzero worker exit')
            result.update(parsed)
        except (ValueError, IndexError):
            result.update(verdict='error', error=(folder / 'stderr.log').read_text()[-2000:])
    (folder / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def report(out: Path, rows: list[dict], complete: bool) -> None:
    lines = ['# Milestone 1 and 3: equivalence checker measurements', '',
             'Status: ' + ('complete.' if complete else 'running; results below are partial.'), '',
             'Exact TZAP -O1 pairs from the accepted Lean harness runs. Milestone 1 has',
             '48 qubits and 4,459/2,703 gates; milestone 3 has 192 qubits and',
             '70,075/41,547 gates. Both Lean runs were independently accepted.', '',
             'Each checker receives one hour and 16 GiB of sampled process-tree RSS.',
             'Checks run sequentially. Time includes imports and circuit loading.',
             'RSS is sampled every 0.25 seconds, so short peaks can be missed.',
             'The deadline uses calendar wall time, including system sleep. An earlier',
             'attempt used the macOS monotonic clock and was discarded without a',
             'verdict; its logs remain under interrupted-attempts/monotonic-clock.', '',
             '| Milestone | Checker | Verdict | Wall seconds | Peak RSS GiB |',
             '|---|---|---|---:|---:|']
    for r in rows:
        lines.append(f"| {r['milestone']} | {r['checker']} | {r['verdict']} | "
                     f"{r.get('wall_seconds', '—')} | {r.get('peak_rss_gib', '—')} |")
    lines += ['', 'Versions and machine details: `environment.json`. Exact pairs, QASM hashes,',
              'commands, complete stdout/stderr and per-run results are saved beside this report.',
              '', 'Feynman feynver is not installed (nor is a Haskell toolchain); it is',
              'recorded as not run, not as a failed checker. No additional applicable',
              'checker was installed in the benchmark environment.', '',
              'QCEC uses the existing hard_pair.py default-portfolio and alternating-DD',
              'configurations. PyZX uses verify_equality; false means inconclusive.',
              'QuiZX full_simp is measured separately from full_simp plus stabilizer',
              'decomposition of the closed miter. The latter compares the squared trace',
              'magnitude to 4^n using Scalar.is_one, without a tolerance.', '',
              'A successful external checker result means this pair does not meet the',
              'milestone requirement that every published checker fail. Unavailable tools',
              'and inconclusive runs do not establish that requirement either.', '']
    (out / 'REPORT.md').write_text('\n'.join(lines))


def batch(out: Path, seconds: float, memory_gib: float) -> None:
    out.mkdir(parents=True, exist_ok=True)
    lock = (out / '.lock').open('w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        sys.exit('This comparison batch is already running.')
    env = {'python': sys.version, 'executable': sys.executable, 'platform': platform.platform(),
           'machine': platform.machine(), 'deadline_clock': 'time.time (calendar wall time)', 'library_commit': 'd7ddcf86dc2ca2185861c9a8c832a749a03af689',
           'versions': {p: metadata.version(p) for p in ('mqt.qcec', 'mqt.core', 'pyzx', 'quizx', 'numpy')},
           'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'hard_pair_sha256': hashlib.sha256(Path(hard_pair.__file__).read_bytes()).hexdigest()}
    from mqt import qcec
    env['qcec_default_configuration'] = str(qcec.verify.__globals__['Configuration']())
    env['qcec_dd_overrides'] = {'run_alternating_checker': True,
                                'run_simulation_checker': False, 'run_zx_checker': False}
    (out / 'environment.json').write_text(json.dumps(env, indent=2) + '\n')
    result_file = out / 'results.jsonl'
    rows = [json.loads(s) for s in result_file.read_text().splitlines()] if result_file.exists() else []
    for milestone, run_id in RUNS.items():
        run = Path.home() / '.circuiteq-harness/runs' / run_id
        judged = json.loads((run / 'meta/judge.json').read_text())
        if judged.get('verdict') != 'ACCEPT' or judged.get('claim') != 'equiv':
            raise ValueError(f'Milestone {milestone} lacks independent acceptance')
        pair = json.loads((run / 'meta/pair.json').read_text())
        folder = out / f'milestone-{milestone}'
        folder.mkdir(exist_ok=True)
        (folder / 'pair.json').write_text(json.dumps(pair, indent=2) + '\n')
        hashes = {}
        for side in ('original', 'optimized'):
            gates = [(g.split()[0], *map(int, g.split()[1:])) for g in pair[side]]
            qasm = hard_pair.to_qasm(gates, pair['qubits'], f'milestone-{milestone} {side}')
            assert hard_pair.parse_qasm(qasm) == (pair['qubits'], gates)
            target = folder / f'{side}.qasm'
            target.write_text(qasm)
            hashes[side] = hashlib.sha256(target.read_bytes()).hexdigest()
        (folder / 'sha256.json').write_text(json.dumps(hashes, indent=2) + '\n')
        for checker in (*CHECKERS, 'feynver'):
            if any(r['milestone'] == milestone and r['checker'] == checker for r in rows):
                continue
            status = {'state': 'running', 'milestone': milestone, 'checker': checker,
                      'pid': os.getpid(), 'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
            (out / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
            print(json.dumps(status), flush=True)
            report(out, rows, False)
            if checker == 'feynver':
                result = {'checker': checker, 'verdict': 'not_run',
                          'reason': 'feynver and Haskell toolchain are not installed'}
            else:
                result = measured(checker, folder / 'original.qasm', folder / 'optimized.qasm',
                                  folder / checker, seconds, memory_gib)
            result['milestone'] = milestone
            rows.append(result)
            with result_file.open('a') as f:
                f.write(json.dumps(result) + '\n')
            print(json.dumps(result), flush=True)
            report(out, rows, False)
    report(out, rows, True)
    (out / 'status.json').write_text(json.dumps({'state': 'complete', 'results': len(rows)}, indent=2))


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='mode', required=True)
    w = sub.add_parser('worker')
    w.add_argument('checker', choices=CHECKERS)
    w.add_argument('a', type=Path)
    w.add_argument('b', type=Path)
    w.add_argument('--seconds', type=float, default=3600)
    b = sub.add_parser('batch')
    b.add_argument('--out', required=True, type=Path)
    b.add_argument('--seconds', type=float, default=3600)
    b.add_argument('--memory-gib', type=float, default=16)
    args = p.parse_args()
    if args.mode == 'worker':
        result = (quizx_decompose(args.a, args.b) if args.checker == 'quizx_decompose'
                  else hard_pair.check(args.checker, args.a, args.b, args.seconds))
        print(json.dumps(result), flush=True)
    else:
        batch(args.out.resolve(), args.seconds, args.memory_gib)


if __name__ == '__main__':
    main()
