import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- If `\"` were read as the end of the string, the real closing quote would open a new string
-- that swallows the next line, and the `sorry` there would go unreported.
open Lean in
theorem «findForbidden ends a string at its real closing quote, not at an escaped one» : True := by
  run_tac do
    let source := "def s : String := \"a\\\"b\"\ntheorem t : False := by sorry"
    let found := Gate.findForbidden source
    unless found == [(2, "sorry")] do
      throwError m!"expected exactly [(2, \"sorry\")], got {found}"
  trivial
