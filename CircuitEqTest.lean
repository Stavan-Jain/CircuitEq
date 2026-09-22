/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Examples
import CircuitEqTest.PhasePoly
import CircuitEqTest.Tableau
import CircuitEqTest.Replay

/-!
# The examples and the tests

Built by `lake build` and checked by CI like the library, but not part of
it: nothing in `CircuitEq` imports these, so a consumer of the library does
not build them. `CircuitEq/Examples.lean` is the showcase of worked
identities (it lives beside the modules it demonstrates, and the agent
harness keeps it in a run's workspace); `CircuitEqTest/` holds the checkers'
regression tests, which restate parts of benchmark answers and are removed
from every run's workspace.
-/
