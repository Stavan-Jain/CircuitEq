"""A Python mirror of ``CircuitEq/Certificate.lean``: steps, replay, search.

The certificate language is data, so an external search can run the same
interpreter fast and hand Lean only the trace. This module mirrors, function
for function, ``Step``, ``replay`` and the checks they rely on
(``Instr.CanCommute``, ``Instr.CanCancel``, ``masksDisjoint`` on supports,
``rename`` on a wire list, and the basis evaluator over ``Q(zeta_8)``), and
adds the alignment search of ``CircuitEq/Tactic.lean``: cancel inverse pairs,
place the given windows in order, pull every other gate of the target to the
front, with moves found on the target inverted into a single trace.

Nothing here is trusted. Lean replays the emitted certificate and proves
the equivalence; a step this mirror accepts and ``replay`` rejects is a bug
in the mirror. Positions, take/drop semantics and the order of checks follow
the Lean definitions exactly so that the two agree step by step.

The same steps replay up to a global phase (``replayPhase``): a window then
names the exponent ``p`` with ``a = w^p b`` on its own wires (``findPhase``),
the exponents add modulo eight, and the theorem is stated on ``≡ₚ[k]``.

Usage::

    python scripts/certificate.py tof_3            # print the Lean certificate
    python scripts/certificate.py tof_3 --theorem  # as a complete theorem
    python scripts/certificate.py tof_3 --phase --theorem  # up to phase, named

The benchmark's two circuits are read from the ``def original`` and
``def optimized`` of its Lean module (which ``check_pyzx_benchmarks.py``
compares with the QASM fixtures); its windows are the ones the Lean proof
uses. The emitted certificate is replayed here before it is printed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from alphabet import DIAG, GATES, INVERSE  # noqa: E402, F401  (re-exported to importers)

# ---------------------------------------------------------------------------
# Instructions: ("one", gate, i) or ("cnot", c, t), mirroring `Instr`.

Instr = tuple


def one(g: str, i: int) -> Instr:
    return ("one", g, i)


def cnot(c: int, t: int) -> Instr:
    return ("cnot", c, t)


def support(g: Instr) -> int:
    """`Instr.support`: bit `i` set iff wire `i` is touched."""
    if g[0] == "one":
        return 1 << g[2]
    return (1 << g[1]) | (1 << g[2])


def circuit_support(c: list[Instr]) -> int:
    """`support`: the union of the instruction supports."""
    m = 0
    for g in c:
        m |= support(g)
    return m


def masks_disjoint(a: int, b: int) -> bool:
    """`masksDisjoint`."""
    return a & b == 0


def can_commute(a: Instr, b: Instr) -> bool:
    """`Instr.CanCommute`, clause for clause."""
    if a == b:
        return True
    if a[0] == "one" and b[0] == "one":
        _, g, i = a
        _, g2, j = b
        return i != j or (g in DIAG and g2 in DIAG)
    if a[0] == "one" and b[0] == "cnot":
        _, g, i = a
        _, c, t = b
    elif a[0] == "cnot" and b[0] == "one":
        _, g, i = b
        _, c, t = a
    else:
        _, a1, b1 = a
        _, c1, d1 = b
        return a1 != d1 and c1 != b1
    return (i != c and i != t) or (c != t and ((i == c and g in DIAG) or (i == t and g == "X")))


def can_cancel(a: Instr, b: Instr) -> bool:
    """`Instr.CanCancel`."""
    if a[0] == "one" and b[0] == "one":
        return a[2] == b[2] and b[1] == INVERSE[a[1]]
    if a[0] == "cnot" and b[0] == "cnot":
        return a[1] == b[1] and a[2] == b[2] and a[1] != a[2]
    return False


def rename(wires: list[int], c: list[Instr]) -> list[Instr]:
    """`rename (wiresOf wires _)`: qubit `j` of the small register is `wires[j]`."""
    out = []
    for g in c:
        if g[0] == "one":
            out.append(one(g[1], wires[g[2]]))
        else:
            out.append(cnot(wires[g[1]], wires[g[2]]))
    return out


def wires_of(g: Instr) -> list[int]:
    return [g[2]] if g[0] == "one" else [g[1], g[2]]


# ---------------------------------------------------------------------------
# Q(zeta_8) and the basis evaluator, mirroring `Zeta8`, `Gate1.mat`, `applyOne`,
# `applyCNOT` and `evalChecker`.


class Zeta8:
    """`a + b w + c w^2 + d w^3` with `w^4 = -1`, exact rational coordinates."""

    __slots__ = ("c",)

    def __init__(self, a=0, b=0, c=0, d=0):
        self.c = (Fraction(a), Fraction(b), Fraction(c), Fraction(d))

    def __add__(self, o: "Zeta8") -> "Zeta8":
        return Zeta8(*(x + y for x, y in zip(self.c, o.c)))

    def __neg__(self) -> "Zeta8":
        return Zeta8(*(-x for x in self.c))

    def __mul__(self, o: "Zeta8") -> "Zeta8":
        r = [Fraction(0)] * 4
        for i, x in enumerate(self.c):
            if x == 0:
                continue
            for j, y in enumerate(o.c):
                k = i + j
                if k < 4:
                    r[k] += x * y
                else:
                    r[k - 4] -= x * y
        return Zeta8(*r)

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Zeta8) and self.c == o.c

    def __hash__(self) -> int:
        return hash(self.c)


ZERO = Zeta8()
ONE = Zeta8(1)
OMEGA = Zeta8(0, 1, 0, 0)
IMAG = Zeta8(0, 0, 1, 0)
INV_SQRT2 = Zeta8(0, Fraction(1, 2), 0, Fraction(-1, 2))
MINUS_OMEGA3 = Zeta8(0, 0, 0, -1)

# mat[g][(r, c)] for r, c in {0, 1}, mirroring `Gate1.mat`.
MAT = {
    "H": {(0, 0): INV_SQRT2, (0, 1): INV_SQRT2, (1, 0): INV_SQRT2, (1, 1): -INV_SQRT2},
    "X": {(0, 0): ZERO, (0, 1): ONE, (1, 0): ONE, (1, 1): ZERO},
    "Y": {(0, 0): ZERO, (0, 1): -IMAG, (1, 0): IMAG, (1, 1): ZERO},
    "Z": {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): -ONE},
    "S": {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): IMAG},
    "Sdg": {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): -IMAG},
    "T": {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): OMEGA},
    "Tdg": {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): MINUS_OMEGA3},
}


def apply_instr(g: Instr, psi: list[Zeta8]) -> list[Zeta8]:
    """`Instr.apply` on a materialised state (`evalList`, one instruction)."""
    if g[0] == "one":
        m, i = MAT[g[1]], g[2]
        out = []
        for x, amp in enumerate(psi):
            b = (x >> i) & 1
            out.append(m[(b, b)] * amp + m[(b, 1 - b)] * psi[x ^ (1 << i)])
        return out
    _, c, t = g
    return [psi[x ^ (1 << t)] if (x >> c) & 1 else psi[x] for x in range(len(psi))]


def eval_circuit(c: list[Instr], psi: list[Zeta8]) -> list[Zeta8]:
    for g in c:
        psi = apply_instr(g, psi)
    return psi


def eval_checker(k: int):
    """`evalChecker k`: agree on the `2 ^ k` basis vectors."""

    def check(a: list[Instr], b: list[Instr]) -> bool:
        for y in range(1 << k):
            basis = [ONE if x == y else ZERO for x in range(1 << k)]
            if eval_circuit(a, basis) != eval_circuit(b, basis):
                return False
        return True

    return check


def syntactic_checker(a: list[Instr], b: list[Instr]) -> bool:
    """`syntacticChecker`."""
    return a == b


def default_checkers(k: int):
    """`defaultCheckers`: the basis evaluator at index 0, syntactic equality at 1."""
    return [eval_checker(k), syntactic_checker]


def eval_phase_finder(k: int):
    """`evalPhaseFinder k` (`findPhase`): the first exponent `p` in `0..7` with
    `a = w^p b` on the `2 ^ k` basis vectors, or `None`."""

    def find(a: list[Instr], b: list[Instr]) -> int | None:
        columns = []
        for y in range(1 << k):
            basis = [ONE if x == y else ZERO for x in range(1 << k)]
            columns.append((eval_circuit(a, basis), eval_circuit(b, basis)))
        phase = ONE
        for p in range(8):
            if all(va == [phase * z for z in vb] for va, vb in columns):
                return p
            phase = phase * OMEGA
        return None

    return find


def syntactic_finder(a: list[Instr], b: list[Instr]) -> int | None:
    """`(syntacticChecker k).toFinder`: phase 0 on equal lists."""
    return 0 if a == b else None


def default_phase_finders(k: int):
    """`defaultPhaseFinders`: the basis evaluator with the phase named at index 0
    (an exactly equal window has phase 0, which is what the phase-polynomial
    checker in front of it answers in Lean), syntactic equality at 1."""
    return [eval_phase_finder(k), syntactic_finder]


# ---------------------------------------------------------------------------
# Steps and replay, mirroring `Step`, `replayStep` and `replay`.


@dataclass(frozen=True)
class Swap:
    i: int


@dataclass(frozen=True)
class MoveLeft:
    i: int
    d: int


@dataclass(frozen=True)
class MoveRight:
    i: int
    d: int


@dataclass(frozen=True)
class Cancel:
    i: int


@dataclass(frozen=True)
class Insert:
    i: int
    a: Instr
    b: Instr


@dataclass(frozen=True)
class Window:
    i: int
    wires: tuple
    a: tuple
    b: tuple
    k: int


Step = Swap | MoveLeft | MoveRight | Cancel | Insert | Window


def replay_step(checkers, c: list[Instr], s: Step) -> list[Instr] | None:
    """`replayStep`; `None` when the step is not licensed. Every step walks to
    its position and fails if the circuit is shorter (`rewriteAt`); `MoveLeft`
    walks to `i - d` (truncated at 0) and crosses `min(d, i)` gates."""
    if isinstance(s, Swap):
        suf = c[s.i:]
        if len(suf) >= 2 and can_commute(suf[0], suf[1]):
            return c[:s.i] + [suf[1], suf[0]] + suf[2:]
        return None
    if isinstance(s, MoveLeft):
        suf = c[s.i:]
        if not suf:
            return None
        g, rest = suf[0], suf[1:]
        front = c[:s.i]
        k = max(s.i - s.d, 0)  # Lean's truncated `i - d`
        pre, block = front[:k], front[k:]
        if masks_disjoint(support(g), circuit_support(block)):
            return pre + [g] + block + rest
        return None
    if isinstance(s, MoveRight):
        suf = c[s.i:]
        if not suf:
            return None
        g, rest = suf[0], suf[1:]
        if s.d > len(rest):
            return None
        block, tail = rest[:s.d], rest[s.d:]
        if masks_disjoint(support(g), circuit_support(block)):
            return c[:s.i] + block + [g] + tail
        return None
    if isinstance(s, Cancel):
        suf = c[s.i:]
        if len(suf) >= 2 and can_cancel(suf[0], suf[1]):
            return c[:s.i] + suf[2:]
        return None
    if isinstance(s, Insert):
        if s.i <= len(c) and can_cancel(s.a, s.b):
            return c[:s.i] + [s.a, s.b] + c[s.i:]
        return None
    if isinstance(s, Window):
        placed = place_window(c, s)
        if placed is None:
            return None
        row = checkers(len(s.wires))
        if s.k >= len(row) or not row[s.k](list(s.a), list(s.b)):
            return None
        return placed
    raise TypeError(s)


def place_window(c: list[Instr], s: Window) -> list[Instr] | None:
    """`rewriteAt (placeFront wires a b) i`: the syntactic half of a window, no
    checker consulted."""
    if s.i > len(c):
        return None
    wires = list(s.wires)
    if len(set(wires)) != len(wires):
        return None
    a, b = list(s.a), list(s.b)
    suf = c[s.i:]
    if suf[:len(a)] != rename(wires, a):
        return None
    return c[:s.i] + rename(wires, b) + suf[len(a):]


def replay(checkers, steps: list[Step], c: list[Instr]) -> list[Instr] | None:
    """`replay`."""
    for s in steps:
        c = replay_step(checkers, c, s)
        if c is None:
            return None
    return c


def replay_phase(finders, steps: list[Step], c: list[Instr]) -> tuple[int, list[Instr]] | None:
    """`replayPhase`: the same steps up to a global phase. A window is placed
    syntactically and adds the exponent its finder names, modulo eight; every
    other step is the exact rewrite of `replay_step`. Returns the exponent of
    the total phase and the resulting circuit."""
    phase = 0
    for s in steps:
        if isinstance(s, Window):
            placed = place_window(c, s)
            if placed is None:
                return None
            row = finders(len(s.wires))
            q = row[s.k](list(s.a), list(s.b)) if s.k < len(row) else None
            if q is None:
                return None
            phase, c = (phase + q) % 8, placed
        else:
            c = replay_step(default_checkers, c, s)
            if c is None:
                return None
    return phase, c


# ---------------------------------------------------------------------------
# The search, mirroring the alignment of `CircuitEq/Tactic.lean`.


class Blocked(Exception):
    """A pull the checks do not license."""


def pull_to(side: str, cur: list[Instr], p: int, q: int) -> tuple[list[Instr], list[Step]]:
    """Move the gate at `p` to `q <= p`: one `MoveLeft` per run of disjoint
    gates, one `Swap` per commuting gate on a shared wire."""
    g = cur[p]
    steps: list[Step] = []
    pos, run = p, 0
    for j in range(p - 1, q - 1, -1):
        x = cur[j]
        if masks_disjoint(support(g), support(x)):
            run += 1
            continue
        if run:
            steps.append(MoveLeft(pos, run))
            pos -= run
            run = 0
        ok = can_commute(x, g) if side == "left" else can_commute(g, x)
        if not ok:
            raise Blocked(f"{fmt_instr(g)} is blocked by {fmt_instr(x)}")
        steps.append(Swap(pos - 1))
        pos -= 1
    if run:
        steps.append(MoveLeft(pos, run))
    new = cur[:p] + cur[p + 1:]
    new.insert(q, g)
    return new, steps


def pull_one(side: str, cur: list[Instr], q: int, g: Instr) -> tuple[list[Instr], list[Step]]:
    """Pull the first occurrence of `g` at or after `q` that can be moved to `q`."""
    seen = False
    for p in range(q, len(cur)):
        if cur[p] == g:
            seen = True
            try:
                return pull_to(side, cur, p, q)
            except Blocked:
                continue
    region = fmt_circuit(cur[q:])
    if seen:
        raise Blocked(f"{fmt_instr(g)} is blocked by a gate on its wires in {region}")
    raise Blocked(f"{fmt_instr(g)} does not occur in {region}")


def cancel_pairs(side: str, cur: list[Instr]) -> tuple[list[Instr], list[Step]]:
    """Remove inverse pairs whose second gate can be moved next to the first."""
    for i in range(len(cur)):
        for j in range(i + 1, len(cur)):
            a, b = cur[i], cur[j]
            if not can_cancel(a, b):
                continue
            try:
                moved, moves = pull_to(side, cur, j, i + 1)
            except Blocked:
                continue
            rest, more = cancel_pairs(side, moved[:i] + moved[i + 2:])
            return rest, moves + [Cancel(i)] + more
    return cur, []


def restrict(left: list[Instr], right: list[Instr]) -> tuple[list[int], list[Instr], list[Instr]]:
    """A window's wires in order of first use, and both sides on those wires."""
    wires: list[int] = []
    for g in left + right:
        for w in wires_of(g):
            if w not in wires:
                wires.append(w)
    index = {w: j for j, w in enumerate(wires)}

    def small(g: Instr) -> Instr:
        if g[0] == "one":
            return one(g[1], index[g[2]])
        return cnot(index[g[1]], index[g[2]])

    return wires, [small(g) for g in left], [small(g) for g in right]


def invert(s: Step) -> Step:
    """The inverse of a step found on the target circuit."""
    if isinstance(s, Swap):
        return s
    if isinstance(s, MoveLeft):
        return MoveRight(s.i - s.d, s.d)
    if isinstance(s, MoveRight):
        return MoveLeft(s.i + s.d, s.d)
    if isinstance(s, Cancel):
        raise ValueError("a Cancel on the target needs its pair; use cancel_pairs_target")
    if isinstance(s, Insert):
        return Cancel(s.i)
    raise ValueError("a window step never occurs on the target circuit")


def align(c1: list[Instr], c2: list[Instr], windows: list[tuple[list[Instr], list[Instr]]],
          cancel: bool = False) -> list[Step]:
    """Find a certificate from `c1` to `c2` given the windows in order; with
    `cancel`, first remove inverse pairs on both sides (`circuit_simp`)."""
    steps_l: list[Step] = []
    steps_r: list[Step] = []
    left, right = list(c1), list(c2)
    if cancel:
        left, steps_l = cancel_pairs("left", left)
        right, forward = cancel_pairs("right", right)
        # A `Cancel i` on the target is inverted to `Insert i a b`; record the pair.
        cur = list(c2)
        inv: list[Step] = []
        for s in forward:
            if isinstance(s, Cancel):
                inv.append(Insert(s.i, cur[s.i], cur[s.i + 1]))
            else:
                inv.append(invert(s))
            cur = replay_step(default_checkers, cur, s)
        steps_r = inv
    done = 0
    i = 0
    while True:
        if i < len(windows):
            wl, wr = windows[i]
            try:
                L, R, sl, sr = left, right, [], []
                for j, g in enumerate(wl):
                    L, s = pull_one("left", L, done + j, g)
                    sl += s
                for j, g in enumerate(wr):
                    R, s = pull_one("right", R, done + j, g)
                    sr += s
                wires, a, b = restrict(wl, wr)
                sl.append(Window(done, tuple(wires), tuple(a), tuple(b), 0))
                left = L[:done] + list(wr) + L[done + len(wl):]
                right = R
                steps_l += sl
                steps_r += [invert(s) for s in sr]
                done += len(wr)
                i += 1
                continue
            except Blocked:
                pass
        if done < len(right):
            y = right[done]
            try:
                left, s = pull_one("left", left, done, y)
            except Blocked as e:
                if i < len(windows):
                    raise Blocked(f"{e} (pending window {i + 1})") from None
                raise
            steps_l += s
            done += 1
        else:
            if i < len(windows):
                raise Blocked(f"window {i + 1} could not be placed")
            if len(left) != done:
                raise Blocked(f"unmatched instructions on the left: {fmt_circuit(left[done:])}")
            break
    return steps_l + list(reversed(steps_r))


# ---------------------------------------------------------------------------
# Lean syntax.


def fmt_instr(g: Instr) -> str:
    if g[0] == "one":
        return f"{g[1]} {g[2]}"
    return f"CX {g[1]} {g[2]}"


def fmt_circuit(c) -> str:
    return "[" + ", ".join(fmt_instr(g) for g in c) + "]"


def fmt_step(s: Step) -> str:
    """One step in the surface syntax of `Step n`."""
    if isinstance(s, Swap):
        return f".swap {s.i}"
    if isinstance(s, MoveLeft):
        return f".moveLeft {s.i} {s.d}"
    if isinstance(s, MoveRight):
        return f".moveRight {s.i} {s.d}"
    if isinstance(s, Cancel):
        return f".cancel {s.i}"
    if isinstance(s, Insert):
        return f".insert {s.i} ({fmt_instr(s.a)}) ({fmt_instr(s.b)})"
    if isinstance(s, Window):
        k = len(s.wires)
        return (f".window {s.i} [{', '.join(map(str, s.wires))}] "
                f"({fmt_circuit(s.a)} : Circuit {k}) {fmt_circuit(s.b)} {s.k}")
    raise TypeError(s)


def fmt_certificate(steps: list[Step], indent: int = 4, width: int = 96) -> str:
    """The `List (Step n)` literal, wrapped at `width` columns."""
    lines, line = [], " " * indent + "["
    for j, s in enumerate(steps):
        piece = fmt_step(s) + ("," if j + 1 < len(steps) else "]")
        if len(line) + 1 + len(piece) > width and line.strip() not in ("[", ""):
            lines.append(line.rstrip())
            line = " " * (indent + 2) + piece
        else:
            line += ("" if line.endswith("[") else " ") + piece
    lines.append(line)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Benchmarks.


def parse_lean_instr(text: str) -> Instr:
    parts = text.split()
    if parts[0] == "CX":
        return cnot(int(parts[1]), int(parts[2]))
    if parts[0] not in GATES:
        raise ValueError(f"unknown gate: {text}")
    return one(parts[0], int(parts[1]))


def parse_lean_circuit(text: str) -> list[Instr]:
    text = text.strip()
    if not text:
        return []
    return [parse_lean_instr(g) for g in text.split(",")]


def read_lean_defs(module: Path) -> tuple[int, list[Instr], list[Instr]]:
    """The `original` and `optimized` circuits of a benchmark module."""
    src = module.read_text()
    out = []
    n = None
    for definition in ("original", "optimized"):
        match = re.search(rf"def {definition} : Circuit (\d+) :=\s*\[([^\]]*)\]", src)
        if match is None:
            raise ValueError(f"{module}: missing def {definition}")
        n = int(match[1])
        out.append(parse_lean_circuit(match[2]))
    return n, out[0], out[1]


def W(left: str, right: str) -> tuple[list[Instr], list[Instr]]:
    return parse_lean_circuit(left), parse_lean_circuit(right)


# Module name, windows in order, and whether to cancel inverse pairs first
# (`circuit_simp`). The agent harness replaces the whole table by `{}` in a run's
# workspace, so everything about a benchmark's proof goes inside it.
BENCHMARKS = {
    # `steane_plus` is absent: its Lean proof applies a block theorem before
    # aligning, which is not a certificate step yet.
    "tof_3": ("Tof3", [
        W("T 0, T 0", "S 0"),
        W("H 3, CX 1 3", "H 3, CX 1 3, H 3, H 3"),
        W("H 4, CX 2 4", "H 4, CX 2 4, H 4, H 4"),
        W("Tdg 2, CX 3 2, H 3, CX 1 3", "H 3, CX 1 3, H 3, Tdg 2, CX 3 2, H 3"),
    ], False),
    "rep3_phaseflip": ("Rep3PhaseFlip", [], True),
}


def certify(name: str, phase: bool = False) -> tuple[int, list[Step], int | None]:
    """Search, then replay the result as a check; returns the qubit count, the
    steps and, with `phase`, the exponent of the global phase the replay names."""
    module, windows, cancel = BENCHMARKS[name]
    root = Path(__file__).resolve().parents[1]
    n, c1, c2 = read_lean_defs(root / "CircuitEq" / "Benchmarks" / f"{module}.lean")
    steps = align(c1, c2, windows, cancel=cancel)
    if phase:
        result = replay_phase(default_phase_finders, steps, c1)
        if result is None or result[1] != c2:
            raise RuntimeError(f"{name}: the emitted certificate does not replay to the target")
        return n, steps, result[0]
    if replay(default_checkers, steps, c1) != c2:
        raise RuntimeError(f"{name}: the emitted certificate does not replay to the target")
    return n, steps, None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("benchmark", choices=BENCHMARKS)
    parser.add_argument("--theorem", action="store_true",
                        help="print a complete theorem instead of the step list")
    parser.add_argument("--phase", action="store_true",
                        help="replay up to a global phase and name it (≡ₚ[k])")
    args = parser.parse_args()
    n, steps, exponent = certify(args.benchmark, phase=args.phase)
    body = fmt_certificate(steps)
    if args.theorem and args.phase:
        print(f"theorem original_equiv_optimized : original ≡ₚ[{exponent}] optimized := by")
        print("  circuit_replay_phase defaultPhaseFinders")
        print(body)
    elif args.theorem:
        print("theorem original_equiv_optimized : original ≡ᵤ optimized := by")
        print("  circuit_replay defaultCheckers")
        print(body)
    else:
        print(body)
    kinds = {}
    for s in steps:
        kinds[type(s).__name__] = kinds.get(type(s).__name__, 0) + 1
    summary = ", ".join(f"{v} {k}" for k, v in sorted(kinds.items()))
    tail = f", global phase ω^{exponent}" if args.phase else ""
    print(f"-- {len(steps)} steps on {n} qubits ({summary}); replays to the target{tail}.")


if __name__ == "__main__":
    main()
