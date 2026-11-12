import Lean
import Gate.KeywordScan

-- The `{…}` parts of `s!` and `m!` strings are Lean terms, so a forbidden word there is code.
open Lean in
theorem «findForbidden scans code inside interpolated string braces» : True := by
  run_tac do
    let hidden := "def hidden : String := s!\"{(show Nat from by sorry)}\""
    let nested := "def h : MessageData := m!\"a {f \"x\" (by admit)} b\""
    let plain := "def p (n : Nat) : String := s!\"no sorry here {n}\""
    let g1 := Gate.findForbidden hidden
    let g2 := Gate.findForbidden nested
    let g3 := Gate.findForbidden plain
    unless g1 == [(1, "sorry")] && g2 == [(1, "admit")] && g3 == [] do
      throwError m!"got {repr g1}, {repr g2}, {repr g3}"
  trivial
