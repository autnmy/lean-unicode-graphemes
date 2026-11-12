import Lean
import Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any axiom
-- outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`, `axiom`,
-- `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- A proof by `sorry` depends on `sorryAx`. `Lean.ofReduceBool` stands for any other axiom
-- outside the allowed three.
open Lean in
theorem «disallowedAxioms reports sorryAx and ofReduceBool and keeps the three allowed axioms» : True := by
  run_tac do
    let used := #[``propext, ``sorryAx, ``Classical.choice, `Lean.ofReduceBool, ``Quot.sound]
    let bad := Gate.disallowedAxioms used
    unless bad.length == 2 && bad.contains ``sorryAx && bad.contains `Lean.ofReduceBool do
      throwError m!"expected sorryAx and Lean.ofReduceBool, got {bad}"
    unless (Gate.disallowedAxioms #[``propext, ``Classical.choice, ``Quot.sound]).isEmpty do
      throwError "the three allowed axioms must not be reported"
  trivial
