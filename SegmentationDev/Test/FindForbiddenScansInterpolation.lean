import Lean
import SegmentationDev.Gate.KeywordScan

-- "... and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- The `{…}` part of an `s!` or `m!` string is a Lean term, so a word there is code; the text
-- around it is a string. The inputs are plain string literals, so the scan of this file itself
-- sees no code use.
open Lean in
theorem «findForbidden scans the code inside interpolated strings» : True := by
  run_tac do
    let cases : List (String × List (Nat × String)) := [
      ("def hidden : String := s!\"{(show Nat from by sorry)}\"", [(1, "sorry")]),
      ("def msg (f : String → Nat → String) := m!\"a {f \"x\" (by admit)} b\"", [(1, "admit")]),
      ("def h : MessageData := m!\"a {f \"x\" (by admit)} b\"", [(1, "admit")]),
      ("def ok (n : Nat) : String := s!\"no sorry here {n}\"", []),
      ("def p (n : Nat) : String := s!\"no sorry here {n}\"", [])]
    for (src, expected) in cases do
      let got := SegmentationDev.Gate.findForbidden src
      unless got == expected do
        throwError m!"findForbidden {repr src} gave {repr got}, expected {repr expected}"
  trivial
