import Lean
import Gate.KeywordScan

-- "... and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- The `{…}` part of an interpolated string is a Lean term, so a word there is code; the text
-- around it is a string.
open Lean in
theorem «findForbidden scans the code inside interpolated strings» : True := by
  run_tac do
    let hidden := "def hidden : String := s!\"{(show Nat from by sorry)}\""
    let gotHidden := Gate.findForbidden hidden
    unless gotHidden == [(1, "sorry")] do
      throwError m!"findForbidden on an s! interpolation gave {gotHidden}, expected [(1, sorry)]"
    let nested := "def msg (f : String → Nat → String) := m!\"a {f \"x\" (by admit)} b\""
    let gotNested := Gate.findForbidden nested
    unless gotNested == [(1, "admit")] do
      throwError m!"findForbidden on a nested interpolation gave {gotNested}, expected [(1, admit)]"
    let prose := "def ok (n : Nat) : String := s!\"no sorry here {n}\""
    let gotProse := Gate.findForbidden prose
    unless gotProse.isEmpty do
      throwError m!"findForbidden reported string text outside the braces: {gotProse}"
  trivial
