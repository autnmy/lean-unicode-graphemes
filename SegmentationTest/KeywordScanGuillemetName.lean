import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- The words inside the «…» name are prose and must not count; the proof after it is code.
open Lean in
theorem «findForbidden skips a guillemet name but reports sorry after it on the same line» :
    True := by
  run_tac do
    let source := "theorem «uses no sorry and no axiom» : False := by sorry"
    let found := Gate.findForbidden source
    unless found == [(1, "sorry")] do
      throwError m!"expected exactly [(1, \"sorry\")], got {found}"
  trivial
