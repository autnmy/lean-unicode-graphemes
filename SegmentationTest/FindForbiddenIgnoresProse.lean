import Lean
import Gate.KeywordScan

-- Today's tree holds these words only in comments and «…» theorem names, and uses `decide`
-- widely; none of that is a use in code.
open Lean in
theorem «findForbidden ignores comments, strings, guillemet names and similar tokens» : True := by
  run_tac do
    let clean := [
      "-- uses no sorry and no axiom",
      "/- outer /- sorry -/ still a comment native_decide -/ def x := 1",
      "/-- doc: unsafe extern -/ def y := 2",
      "def s : String := \"axiom admit\"",
      "theorem «uses no sorry and no axiom beyond propext» : True := trivial",
      "example : 1 = 1 := by decide",
      "example : 1 = 1 := by decide +kernel",
      "#print axioms Segmentation.graphemes_join",
      "def n := ``sorryAx"]
    for src in clean do
      let got := Gate.findForbidden src
      unless got.isEmpty do
        throwError m!"findForbidden {repr src} gave {repr got}, expected nothing"
    let after := Gate.findForbidden "/- note -/ theorem t : True := by sorry"
    unless after == [(1, "sorry")] do
      throwError m!"code after a closing comment was not scanned: {repr after}"
  trivial
