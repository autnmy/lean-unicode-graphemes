import Lean
import Gate.KeywordScan

-- "and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- Each source holds a literal whose escapes or quotes could make the scanner lose its place.
-- A word in code after the literal must still be reported, and a word inside one must not be.
open Lean in
theorem «findForbidden keeps its place after escaped char literals, raw strings and throwError strings» :
    True := by
  run_tac do
    let cases : List (String × List (Nat × String)) := [
      ("def b := '\\\\'\ntheorem t : False := by sorry", [(2, "sorry")]),
      ("def q := '\\''\ntheorem t : False := by sorry", [(2, "sorry")]),
      ("def p := r\"\\\"\ntheorem t : False := by sorry", [(2, "sorry")]),
      ("def quoted : String := r#\"\"\"#\ntheorem unnoticed : False := by sorry\n", [(2, "sorry")]),
      ("def s := r\"sorry\"", []),
      ("def s := r#\"a \"sorry\" b\"#", []),
      ("def e := throwError \"x {(show Nat from by sorry)}\"", [(1, "sorry")]),
      ("def e := throwErrorAt stx \"x {(show Nat from by sorry)}\"", [(1, "sorry")]),
      ("def e := throwErrorAt (f x) \"x {(show Nat from by sorry)}\"", [(1, "sorry")]),
      ("def e := trace[cls] \"x {(show Nat from by sorry)}\"", [(1, "sorry")]),
      ("def e := throwError \"no sorry here\"", [])]
    for (src, expected) in cases do
      let got := Gate.findForbidden src
      unless got == expected do
        throwError m!"findForbidden {repr src} gave {repr got}, expected {repr expected}"
  trivial
