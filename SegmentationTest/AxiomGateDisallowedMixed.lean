import Lean
import Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- A proof by `sorry` depends on `sorryAx`. `Lean.ofReduceBool` stands for any other axiom
-- outside the allowed three.
-- Allowed axioms in the same list must not mask them, and allowed ones must not be reported.
open Lean in
theorem «disallowedAxioms reports sorryAx and Lean.ofReduceBool mixed with allowed axioms» :
    True := by
  run_tac do
    let used := #[``propext, ``sorryAx, ``Classical.choice, `Lean.ofReduceBool, ``Quot.sound]
    let bad := Gate.disallowedAxioms used
    unless bad.length == 2 && bad.contains ``sorryAx && bad.contains `Lean.ofReduceBool do
      throwError m!"expected exactly sorryAx and Lean.ofReduceBool, got {bad}"
  trivial
