import Lean
import SegmentationDev.Gate.KeywordScan

-- "... and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- Each word is reported once per use, with its line, in line order. A word placed second in an
-- attribute list, or after a line comment, is still code: a pattern that only looks for `@[extern`
-- at the start of the list would miss it. The inputs are plain string literals, so the scan of
-- this file itself sees no code use.
open Lean in
theorem «findForbidden reports each of the seven words used as code with its line» : True := by
  run_tac do
    let cases : List (String × List (Nat × String)) := [
      ("theorem t : True := by\n  sorry", [(2, "sorry")]),
      ("theorem t : True := by admit", [(1, "admit")]),
      ("axiom foo : False", [(1, "axiom")]),
      ("example : 2 + 2 = 4 := by native_decide", [(1, "native_decide")]),
      ("def g := 0\n@[implemented_by g] def f : Nat := 0", [(2, "implemented_by")]),
      ("@[simp, extern \"c_f\"] def f : Nat := 0", [(1, "extern")]),
      ("unsafe def f : Nat := 0", [(1, "unsafe")]),
      ("theorem a : False := by sorry\n" ++
        "theorem b : False := by admit\n" ++
        "axiom c : False\n" ++
        "theorem d : 1 = 1 := by native_decide\n" ++
        "@[implemented_by f] def e := 1\n" ++
        "@[simp, extern \"c\"] def g := 1\n" ++
        "unsafe def h := 1\n",
        [(1, "sorry"), (2, "admit"), (3, "axiom"), (4, "native_decide"), (5, "implemented_by"),
          (6, "extern"), (7, "unsafe")]),
      ("@[simp, extern \"c\"] def f : Nat := 0\n-- a note\nunsafe def g : Nat := 1\n" ++
        "@[inline, implemented_by g] def h : Nat := 1",
        [(1, "extern"), (3, "unsafe"), (4, "implemented_by")])]
    for (src, expected) in cases do
      let got := SegmentationDev.Gate.findForbidden src
      unless got == expected do
        throwError m!"findForbidden {repr src} gave {repr got}, expected {repr expected}"
  trivial
