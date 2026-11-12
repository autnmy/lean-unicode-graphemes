import Lean
import Gate.KeywordScan

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
-- The `{…}` part of an `s!` string is a Lean term, so a scanner that skips whole strings would
-- let this definition through while CI stays green.
open Lean in
theorem «findForbidden reports sorry hidden inside an interpolated string» : True := by
  run_tac do
    let source := "def hidden : String := s!\"{(show Nat from by sorry)}\""
    let found := Gate.findForbidden source
    unless found.contains (1, "sorry") do
      throwError m!"expected (1, \"sorry\") from the interpolated term, got {found}"
  trivial
