import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- Lean block comments nest. A scanner that ends the comment at the first `-/` would report the
-- `sorry` still inside the outer comment; one that never leaves it would miss the `admit`.
open Lean in
theorem «findForbidden tracks nested block comments and still reports admit on the next line» :
    True := by
  run_tac do
    let source := "/- outer /- inner -/ still a comment, no sorry -/\ntheorem t : False := by admit"
    let found := Gate.findForbidden source
    unless found == [(2, "admit")] do
      throwError m!"expected exactly [(2, \"admit\")], got {found}"
  trivial
