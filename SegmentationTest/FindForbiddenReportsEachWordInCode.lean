import Lean
import Gate.KeywordScan

-- "... and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
open Lean in
theorem «findForbidden reports each of the seven words used as code with its line» : True := by
  run_tac do
    let source := "theorem a : False := by sorry\n" ++
      "theorem b : False := by admit\n" ++
      "axiom c : False\n" ++
      "theorem d : 1 = 1 := by native_decide\n" ++
      "@[implemented_by f] def e := 1\n" ++
      "@[simp, extern \"c\"] def g := 1\n" ++
      "unsafe def h := 1\n"
    let got := Gate.findForbidden source
    let expected : List (Nat × String) := [(1, "sorry"), (2, "admit"), (3, "axiom"),
      (4, "native_decide"), (5, "implemented_by"), (6, "extern"), (7, "unsafe")]
    unless got == expected do
      throwError m!"findForbidden gave {got}, expected {expected}"
  trivial
