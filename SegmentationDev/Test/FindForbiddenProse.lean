import Lean
import SegmentationDev.Gate.KeywordScan

-- "... and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- Comments, plain string text and «…» names are prose, so they are not reported; `decide`,
-- `sorryAx` and `axioms` are different tokens from the forbidden words. Skipping prose must stop
-- where the prose ends, so code after a closed comment, an escaped quote or a «…» name is still
-- scanned. The inputs are plain string literals, so the scan of this file itself sees no code use.
open Lean in
theorem «findForbidden skips comments, strings and quoted names but scans the code after them» :
    True := by
  run_tac do
    let cases : List (String × List (Nat × String)) := [
      ("-- uses no sorry and no axiom", []),
      ("/- outer /- sorry -/ still a comment native_decide -/ def x := 1", []),
      ("/-- doc: unsafe extern -/ def y := 2", []),
      ("def s : String := \"axiom admit\"", []),
      ("theorem «uses no sorry and no axiom beyond propext» : True := trivial", []),
      ("example : 1 = 1 := by decide", []),
      ("example : 1 = 1 := by decide +kernel", []),
      ("#print axioms Segmentation.graphemes_join", []),
      ("def n := ``sorryAx", []),
      ("/- note -/ theorem t : True := by sorry", [(1, "sorry")]),
      ("-- uses no sorry\n" ++
        "/- /- sorry -/ axiom -/\n" ++
        "/-- doc: native_decide and unsafe -/\n" ++
        "def s : String := \"axiom\"\n" ++
        "theorem «uses no sorry and no axiom» : True := trivial\n" ++
        "theorem t : 1 = 1 := by decide\n" ++
        "theorem u : 1 = 1 := by decide +kernel\n" ++
        "#check ``sorryAx\n" ++
        "#print axioms t\n", []),
      ("def x := 1\ntheorem v : False := /- x -/ by sorry\n", [(2, "sorry")]),
      ("/- outer /- inner -/ still outer -/ axiom bad : False", [(1, "axiom")]),
      ("/- harmless note -/ theorem t : False := by sorry", [(1, "sorry")]),
      -- Block comments nest: ending at the first `-/` would report the inner word, and never
      -- leaving the comment would miss the `admit`.
      ("/- outer /- inner -/ still a comment, no sorry -/\ntheorem t : False := by admit",
        [(2, "admit")]),
      -- Reading `\"` as the end of the string would swallow the next line's `sorry`.
      ("def s : String := \"a\\\"b\"\ntheorem t : False := by sorry", [(2, "sorry")]),
      ("theorem «uses no sorry and no axiom» : False := by sorry", [(1, "sorry")])]
    for (src, expected) in cases do
      let got := SegmentationDev.Gate.findForbidden src
      unless got == expected do
        throwError m!"findForbidden {repr src} gave {repr got}, expected {repr expected}"
  trivial
