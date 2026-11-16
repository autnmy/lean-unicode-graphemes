import Lean
import Segmentation

-- "`Segmentation/Statements.lean` is byte-for-byte unchanged, and every new helper is in the
-- plain-definition check and the axiom gate."
-- The gate allows only `propext`, `Classical.choice` and `Quot.sound`; `sorry` would show as
-- `sorryAx` and `native_decide` as its own axiom.
open Lean in
/-- The ASCII decision, the ASCII state and the two lemmas that tie them to the general path use only the standard axioms. -/
theorem slice_ascii_helpers_and_lemmas_pass_axiom_gate : True := by
  run_tac do
    let env ← getEnv
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for name in [``Segmentation.asciiBreaksBefore, ``Segmentation.asciiState,
        ``Segmentation.breaksBeforeFast_asciiProps, ``Segmentation.ScanState.push_asciiProps] do
      unless env.contains name do
        throwError m!"{name} is missing"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError m!"{name} depends on the axiom {ax}"
  trivial
