import Lean
import Gate.KeywordScan

-- "... and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- Comments, plain string text and «» names are prose, so they are not reported; `decide`,
-- `sorryAx` and `axioms` are different tokens from the forbidden words.
open Lean in
theorem «findForbidden ignores comments, plain strings, quoted names and decide but not code after a comment» :
    True := by
  run_tac do
    let prose := "-- uses no sorry\n" ++
      "/- /- sorry -/ axiom -/\n" ++
      "/-- doc: native_decide and unsafe -/\n" ++
      "def s : String := \"axiom\"\n" ++
      "theorem «uses no sorry and no axiom» : True := trivial\n" ++
      "theorem t : 1 = 1 := by decide\n" ++
      "theorem u : 1 = 1 := by decide +kernel\n" ++
      "#check ``sorryAx\n" ++
      "#print axioms t\n"
    let gotProse := Gate.findForbidden prose
    unless gotProse.isEmpty do
      throwError m!"findForbidden reported prose or a different token: {gotProse}"
    let afterComment := "def x := 1\ntheorem v : False := /- x -/ by sorry\n"
    let gotAfter := Gate.findForbidden afterComment
    unless gotAfter == [(2, "sorry")] do
      throwError m!"findForbidden after a closing comment gave {gotAfter}, expected [(2, sorry)]"
  trivial
