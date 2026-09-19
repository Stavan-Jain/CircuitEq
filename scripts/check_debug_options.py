"""Early-warning text guard: no ``debug.*`` option in the Lean sources.

``debug.skipKernelTC`` makes Lean add declarations to the environment without
sending them to the kernel. Every leaf proof of this library is
``decide +kernel``, which leaves its whole check to the kernel, so with the
option set a false claim elaborates without an error, and
``scripts/AxiomCheck.lean`` reports it clean: it depends on no axioms at all.
No ``debug.*`` option has a place in a proof library, so this script fails if
one is set in the Lean sources or in the Lake configuration.

This guard is NOT sound, and it is not the defence. An option can be set from
meta code under a name no text search recognises (a ``Name`` assembled from
string pieces, an escaped TOML key), and meta code can add a declaration
unchecked without setting any option. The defence is the kernel replay CI
runs after the build, ``lake env leanchecker CircuitEq``, which re-checks
every declaration of the built ``.olean`` files and which no option can
switch off (CLAUDE.md, "Conventions"; README.md, "Trust"). This script only
reports the obvious spellings early, with a file and a line, before a build
is paid for.

Scanned by default: ``CircuitEq.lean``, every ``.lean`` file under
``CircuitEq/`` and ``scripts/``, and ``lakefile.toml`` / ``lakefile.lean``.
Reported:

* ``set_option`` of any ``debug.*`` option, also behind ``weak.``;
* the names ``skipKernelTC`` and ``addDeclWithoutChecking`` anywhere at all,
  which covers meta code, and docstrings too;
* in the Lake configuration, a ``-D`` flag or an option key for a ``debug.*``
  option.

Comments are scanned like code: a parser for Lean's nested comments would
only be one more thing to get wrong here. The one exempt file is the
regression fixture ``scripts/SkipKernelTCFixture.lean``, which holds the
repro on purpose. When paths are given on the command line exactly those
files are scanned, with no exemption; that is how
``scripts/check_replay_fixture.sh`` asserts the guard still sees the fixture.

    python3 scripts/check_debug_options.py                  # the policy
    python3 scripts/check_debug_options.py FILE [FILE ...]  # just these

Exit status: 0 clean, 1 findings, 2 usage error or nothing to scan.
"""

import os
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent

# The one file allowed to hold the repro.
FIXTURE = Path("scripts/SkipKernelTCFixture.lean")

CONFIG_NAMES = ("lakefile.toml", "lakefile.lean")

UNCHECKED_NAMES = (
    re.compile(r"skipKernelTC|addDeclWithoutChecking"),
    "names a way to add declarations without the kernel",
)

LEAN_RULES = [
    (re.compile(r"set_option\s+(?:weak\.)?debug\."), "sets a `debug.*` option"),
    UNCHECKED_NAMES,
]

CONFIG_RULES = [
    (re.compile(r"-D\s*(?:weak\.)?debug\."), "passes a `-D` flag for a `debug.*` option"),
    (re.compile(r"(?<![A-Za-z0-9_])debug[ \t]*[.\]={]"), "has a `debug.*` option key"),
    UNCHECKED_NAMES,
]


def default_files() -> list[Path]:
    """The files the policy covers, without the fixture."""
    files = [ROOT / "CircuitEq.lean"]
    files += sorted((ROOT / "CircuitEq").rglob("*.lean"))
    files += sorted((ROOT / "scripts").rglob("*.lean"))
    files += [ROOT / name for name in CONFIG_NAMES]
    return [f for f in files if f.is_file() and f.relative_to(ROOT) != FIXTURE]


def scan(path: Path) -> list[tuple[int, str, str]]:
    """Findings in one file, as ``(line number, message, source line)``.

    Guillemets are dropped before matching, and quotes too in the Lake
    configuration, so ``debug.«skipKernelTC»`` and ``"debug".skipKernelTC``
    read as the names they denote. Neither removal changes a line number.
    """
    is_config = path.name in CONFIG_NAMES
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    normal = text.replace("«", "").replace("»", "")
    if is_config:
        normal = normal.replace('"', "").replace("'", "")
    found: dict[int, list[str]] = {}
    for pattern, message in CONFIG_RULES if is_config else LEAN_RULES:
        for match in pattern.finditer(normal):
            number = normal.count("\n", 0, match.start()) + 1
            if message not in found.setdefault(number, []):
                found[number].append(message)
    return [(n, "; ".join(found[n]), lines[n - 1].strip()) for n in sorted(found)]


def display(path: Path) -> str:
    """The path relative to the repository when it lies inside it."""
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def main(argv: list[str]) -> int:
    """Scan the policy's files, or exactly the files named in ``argv``."""
    if any(arg.startswith("-") for arg in argv):
        print(__doc__, file=sys.stderr)
        return 2
    files = [Path(arg) for arg in argv] if argv else default_files()
    missing = [str(f) for f in files if not f.is_file()]
    if missing:
        print(f"no such file: {', '.join(missing)}", file=sys.stderr)
        return 2
    if not argv:
        scanned = {f.relative_to(ROOT).as_posix() for f in files}
        if "CircuitEq.lean" not in scanned or not scanned & set(CONFIG_NAMES):
            print(f"nothing to scan: no CircuitEq.lean or lakefile under {ROOT}", file=sys.stderr)
            return 2
    findings = 0
    for path in files:
        for number, message, source in scan(path):
            findings += 1
            print(f"{display(path)}:{number}: {message}\n    {source}")
            if os.environ.get("GITHUB_ACTIONS") == "true":
                print(f"::error file={display(path)},line={number}::{message}")
    if findings:
        print(
            f"\nDEBUG-OPTION GUARD: {findings} finding(s) in {len(files)} file(s).\n"
            "`debug.skipKernelTC` switches the kernel off, and the axiom check cannot\n"
            "see it; no `debug.*` option belongs in this library (CLAUDE.md,\n"
            "\"Conventions\"). Remove it. This guard is an early warning only: the\n"
            "kernel replay (`lake env leanchecker CircuitEq`) is the defence."
        )
        return 1
    print(f"debug-option guard OK: {len(files)} files scanned, no `debug.*` option set")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
