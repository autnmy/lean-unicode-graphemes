import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- A scanner that drops the rest of a line once it sees a comment would miss the tactic here.
open Lean in
theorem «findForbidden reports code after a closing block comment on the same line» : True := by
  run_tac do
    let source := "/- harmless note -/ theorem t : False := by sorry"
    let found := Gate.findForbidden source
    unless found.contains (1, "sorry") do
      throwError m!"expected (1, \"sorry\") after the closing -/, got {found}"
  trivial
