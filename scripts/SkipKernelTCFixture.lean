/-
Regression fixture for the kernel-replay policy. See CLAUDE.md,
"Conventions", and README.md, "Trust".

`debug.skipKernelTC` makes Lean add a declaration to the environment without
sending it to the kernel. `decide +kernel` leaves its whole check to the
kernel, so with the option set the false theorem below elaborates without an
error, and the axiom policy of `scripts/AxiomCheck.lean` cannot see it: the
theorem depends on no axioms at all. Every leaf proof of the library is a
`decide +kernel`, so this is the library's one real soundness hole, and the
defence is to replay the built `.olean` files through the kernel
(`lake env leanchecker CircuitEq`, in CI), which no option can switch off.

`scripts/check_replay_fixture.sh`, run in CI, asserts three things about this
file: it still compiles without an error (the hole is still open in this
toolchain), the text guard `scripts/check_debug_options.py` flags it, and
`leanchecker` rejects its `.olean` with a kernel error. If the last one ever
stops holding, the replay no longer defends the library.

Not part of any `lean_lib` and never imported, so `lake build` does not see
it, and the one file the text guard exempts. Do not copy it into the library.
-/

set_option debug.skipKernelTC true in
theorem bad : (2 : Nat) + 2 = 5 := by decide +kernel

#print axioms bad   -- prints: 'bad' does not depend on any axioms
