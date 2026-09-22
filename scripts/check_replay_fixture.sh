#!/usr/bin/env bash
# Regression test for the kernel-replay policy (CLAUDE.md, "Conventions";
# README.md, "Trust"). Run from CI after the build:
#
#     scripts/check_replay_fixture.sh
#
# `scripts/SkipKernelTCFixture.lean` proves `2 + 2 = 5` by `decide +kernel`
# under `set_option debug.skipKernelTC true`. This script asserts, in order:
#
#   1. the fixture compiles without an error and `#print axioms` reports no
#      axioms, so the hole is still open in this toolchain and the axiom
#      check is still blind to it. If this starts failing, Lean has changed:
#      re-examine the policy, do not delete the assertion;
#   2. the text guard `scripts/check_debug_options.py` flags the fixture;
#   3. `leanchecker` rejects the fixture's `.olean`, and the rejection comes
#      from the kernel, not from a missing file or a bad search path.
#
# The third assertion is the one that matters: it shows that the replay CI runs
# over the library (`lake env leanchecker CircuitEq CircuitEqTest`) would reject the same
# declaration in a library module. The fixture is not part of any `lean_lib`;
# its `.olean` goes to a temporary directory and nothing is left behind.
set -euo pipefail
cd "$(dirname "$0")/.."

fixture=scripts/SkipKernelTCFixture.lean
module=SkipKernelTCFixture
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

fail() {
  echo "REPLAY FIXTURE FAILED: $1" >&2
  exit 1
}

echo "1. compiling $fixture (expected: no error, no axioms)"
lake env lean -o "$tmp/$module.olean" "$fixture" >"$tmp/compile.log" 2>&1 \
  || { cat "$tmp/compile.log"; fail "the fixture no longer compiles; has Lean closed the hole?"; }
sed 's/^/    /' "$tmp/compile.log"
grep -q "'bad' does not depend on any axioms" "$tmp/compile.log" \
  || fail "'#print axioms bad' no longer reports a clean theorem"

echo "2. text guard on $fixture (expected: findings)"
if python3 scripts/check_debug_options.py "$fixture" >"$tmp/guard.log" 2>&1; then
  cat "$tmp/guard.log"
  fail "the text guard accepted the fixture"
fi
grep -q "sets a \`debug\.\*\` option" "$tmp/guard.log" \
  || { cat "$tmp/guard.log"; fail "the text guard failed for another reason"; }
echo "    flagged"

echo "3. kernel replay of $module.olean (expected: kernel error)"
if lake env env LEAN_PATH="$tmp" leanchecker "$module" >"$tmp/replay.log" 2>&1; then
  cat "$tmp/replay.log"
  fail "leanchecker ACCEPTED a proof of 2 + 2 = 5; the replay is not a defence"
fi
sed 's/^/    /' "$tmp/replay.log"
grep -q "(kernel)" "$tmp/replay.log" \
  || fail "leanchecker failed, but not with a kernel error"

echo "replay fixture OK: compiled clean, flagged by the guard, rejected by the kernel"
