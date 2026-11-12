import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- A pattern that only looks for `@[extern` at the start of the list would miss this form.
open Lean in
theorem «findForbidden reports extern inside an attribute list after another attribute» :
    True := by
  run_tac do
    let source := "@[simp, extern \"c_f\"] def f : Nat := 0"
    let found := Gate.findForbidden source
    unless found == [(1, "extern")] do
      throwError m!"expected exactly [(1, \"extern\")], got {found}"
  trivial
