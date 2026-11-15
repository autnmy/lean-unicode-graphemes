import Lean
import SegmentationDev.KeywordScan

-- "and on any of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or
-- `unsafe` in project code."
-- The scanned sources are written to a temporary directory as string data, so no forbidden
-- word appears as code in this file. Every file is removed before the proof ends.
open Lean in
theorem keyword_scan_main_exits_one_on_forbidden_word_zero_on_clean_one_on_no_paths :
    True := by
  run_tac do
    let dir : System.FilePath := ".lake" / "keyword-scan-acceptance"
    IO.FS.createDirAll dir
    let words := ["sorry", "admit", "native_decide"]
    let mut failures : List String := []
    for w in words do
      let path := dir / s!"{w}.lean"
      IO.FS.writeFile path s!"theorem t : True := by {w}\n"
      let code ← main [path.toString]
      unless code == 1 do failures := failures ++ [s!"{w}: exit {code}"]
    let decls := [("axiom", "axiom a : False\n"), ("unsafe", "unsafe def f : Nat := 0\n"),
      ("extern", "@[extern \"c_f\"] def g : Nat := 0\n"),
      ("implemented_by", "@[implemented_by g] def h : Nat := 0\n")]
    for (w, src) in decls do
      let path := dir / s!"{w}.lean"
      IO.FS.writeFile path src
      let code ← main [path.toString]
      unless code == 1 do failures := failures ++ [s!"{w}: exit {code}"]
    let clean := dir / "clean.lean"
    IO.FS.writeFile clean "-- no sorry here\ntheorem c : 1 = 1 := by decide\n"
    let cleanCode ← main [clean.toString]
    let emptyCode ← main []
    -- A clean file must not reset a failure found in another, in either order, and a path that
    -- cannot be read must fail alone and beside a clean file.
    let forbidden := dir / "sorry.lean"
    let missing := dir / "missing.lean"
    let mixed := [[clean, forbidden], [forbidden, clean], [missing], [clean, missing],
      [missing, clean]]
    let mut mixedFailures : List String := []
    for paths in mixed do
      let code ← main (paths.map (·.toString))
      unless code == 1 do mixedFailures := mixedFailures ++ [s!"{paths}: exit {code}"]
    IO.FS.removeDirAll dir
    unless mixedFailures.isEmpty do throwError "multi-path runs not rejected: {mixedFailures}"
    unless failures.isEmpty do throwError "forbidden words not rejected: {failures}"
    unless cleanCode == 0 do throwError "clean file exited {cleanCode}"
    unless emptyCode == 1 do throwError "no paths exited {emptyCode}"
  trivial
