import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any axiom
-- outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`, `axiom`,
-- `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- Skipping comments must stop at the comment's end, nested comments included, so code placed
-- after the closing marker is still scanned.
open Lean in
theorem «findForbidden reports code that follows a closed block comment on the same line» : True := by
  run_tac do
    let found := Gate.findForbidden "/- outer /- inner -/ still outer -/ axiom bad : False"
    unless found == [(1, "axiom")] do
      throwError m!"expected [(1, axiom)], got {found}"
  trivial
