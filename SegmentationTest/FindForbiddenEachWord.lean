import Lean
import Gate.KeywordScan

-- "and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- The inputs are plain string literals, so the scan of this file itself sees no code use.
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
      ("unsafe def f : Nat := 0", [(1, "unsafe")])]
    for (src, expected) in cases do
      let got := Gate.findForbidden src
      unless got == expected do
        throwError m!"findForbidden {repr src} gave {repr got}, expected {repr expected}"
  trivial
