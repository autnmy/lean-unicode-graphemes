import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any axiom
-- outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`, `axiom`,
-- `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- The `{…}` part of an interpolated string is a Lean term, so a tactic inside it is code.
open Lean in
theorem «findForbidden reports sorry hidden inside an interpolated string» : True := by
  run_tac do
    let found := Gate.findForbidden "def hidden : String := s!\"{(show Nat from by sorry)}\""
    unless found.contains (1, "sorry") do
      throwError m!"expected (1, sorry), got {found}"
  trivial
