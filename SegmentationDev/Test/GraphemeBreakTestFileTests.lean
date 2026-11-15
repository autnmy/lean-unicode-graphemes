import SegmentationDev.Test.GraphemeBreakTestFile

/-!
# Tests of the GraphemeBreakTest.txt reader

The parser, the count check and the comparison that `checkGraphemeBreakTest` in
`SegmentationDev.Test.DataChecks` runs over the real file, checked here on small inputs.
-/

open SegmentationDev.Test.GraphemeBreakTestFile

/-! ## Parsing a test line -/

-- The expected clusters come from the file's ÷ and × markers, never from the segmenter.
-- The comment line is not a test line, so the data line is physical line 2.
theorem «parseTestFile reads expected clusters from the markers, astral code points included» :
    (match parseTestFile "# header\n÷ 1F1E6 × 1F1E7 ÷ 0020 ÷\t# x\n" with
      | .ok [c] =>
        c.line == 2 && c.codePoints == [0x1F1E6, 0x1F1E7, 0x0020] &&
          c.expected == [[0x1F1E6, 0x1F1E7], [0x0020]]
      | _ => false) = true := by
  decide

-- Comment-only and blank lines are not test lines, and line numbers count them.
#guard (parseTestFile ("# header\n\n#\n" ++ "÷ 0041 ÷ 0042 ÷\t# ok\n" ++ "# Lines: 1\n")).toOption.map
  (·.map (·.line)) == some [4]

-- Empty text holds no test lines; `checkCounts` is what makes that a failure.
#guard (parseTestFile "").toOption.map (·.length) == some 0

/-! ## Rejecting a bad line

Each bad line sits after a valid one, and the valid line alone parses, so a failure comes from
the bad line and not from an empty result. A skipped bad line would let the conformance run
check less than the whole file.
-/

/-- The valid first line of every input below. -/
def graphemeBreakTestValidLine : String := "÷ 0041 ÷ 0042 ÷\t# ok\n"

#guard (parseTestFile graphemeBreakTestValidLine).toOption.map (·.length) == some 1

-- A line without its leading break marker; the error names the bad line's number.
#guard parseTestFile (graphemeBreakTestValidLine ++ "0041 × 0042 ÷\t# bad\n") matches
  .error "line 2 is not a GraphemeBreakTest.txt test line: 0041 × 0042 ÷"

-- A token that is not hexadecimal.
#guard parseTestFile (graphemeBreakTestValidLine ++ "# comment\n÷ 00ZZ ÷\t# bad\n") matches
  .error "line 3 is not a GraphemeBreakTest.txt test line: ÷ 00ZZ ÷"

-- Two markers in a row, so a code point is missing between them.
#guard !(parseTestFile (graphemeBreakTestValidLine ++ "÷ 0041 × ÷\t# bad\n")).toBool

-- A line holding only the break marker has no code point at all.
#guard !(parseTestFile (graphemeBreakTestValidLine ++ "÷\t# bad\n")).toBool

-- Only ÷ and × are markers; a "+" must fail the parse, not be read as either.
theorem «parseTestFile rejects a line with an unknown marker beside a valid line» :
    (parseTestFile (graphemeBreakTestValidLine ++ "÷ 0041 + 0042 ÷\t# bad\n")).toBool = false := by
  decide +kernel

-- Every line of the file ends with ÷ (the break at the end of the text). A line without it has
-- no defined last cluster, so it must fail instead of being guessed at or skipped.
theorem «parseTestFile rejects a line without its trailing break marker beside a valid line» :
    (parseTestFile (graphemeBreakTestValidLine ++ "÷ 0041 × 0042\t# bad\n")).toBool = false := by
  decide +kernel

-- D800 is a surrogate, not a valid Char. Char.ofNat would quietly turn it into U+0000, so the
-- parser must refuse it rather than test the segmenter on a different code point.
theorem «parseTestFile rejects a surrogate code point beside a valid line» :
    (parseTestFile (graphemeBreakTestValidLine ++ "÷ D800 ÷\t# bad\n")).toBool = false := by
  decide +kernel

-- 110000 is past the last Unicode code point, so it is not a valid Char and the line must fail.
theorem «parseTestFile rejects a code point above 10FFFF beside a valid line» :
    (parseTestFile (graphemeBreakTestValidLine ++ "÷ 110000 ÷\t# bad\n")).toBool = false := by
  decide +kernel

/-! ## Counting the test lines -/

-- The count the file states in its own trailer is what the parsed count is checked against.
theorem «statedLineCount reads 853 from the file's Lines trailer» :
    (statedLineCount "÷ 0020 ÷ 0020 ÷\t# x\n#\n# Lines: 853\n#\n# EOF\n" == some 853 &&
      statedLineCount "÷ 0020 ÷ 0020 ÷\t# x\n# EOF\n" == none) = true := by
  decide

theorem «checkCounts accepts 853 parsed lines when the file states 853» :
    (checkCounts 853 (some 853)).toBool = true := by
  decide

-- A parser that silently skips one line must not pass.
theorem «checkCounts rejects a parse that dropped a line the file states» :
    (checkCounts 852 (some 853)).toBool = false := by
  decide

-- A file cut to 852 lines whose trailer was edited to agree must still fail:
-- agreeing with the trailer alone is not enough, the count must be 853.
theorem «checkCounts rejects a file truncated with a matching trailer» :
    (checkCounts 852 (some 852)).toBool = false := by
  decide

-- A run that compared nothing must fail rather than pass with zero mismatches.
theorem «checkCounts rejects an empty parse with an empty trailer» :
    (checkCounts 0 (some 0)).toBool = false := by
  decide

-- Without the file's own "# Lines:" trailer there is nothing independent to
-- check the parsed count against, so the check must fail rather than pass.
theorem «checkCounts rejects 853 parsed lines when the file states no count» :
    (checkCounts 853 none).toBool = false := by
  decide

/-! ## Rendering the case module -/

/-- A two-line test file whose trailer claims the full 853 lines. -/
def graphemeBreakTestTwoLinesClaiming853 : String :=
  "÷ 0020 ÷ 0020 ÷\t# x\n÷ 0061 × 0308 ÷\t# y\n#\n# Lines: 853\n#\n# EOF\n"

-- A truncated file must never become the data a proof reads; the error names both counts.
#guard renderCasesModule "licence" graphemeBreakTestTwoLinesClaiming853 matches
  .error "parsed 2 test lines, but the file states 853"

-- Without its "# Lines:" trailer the file has nothing to check the parsed count against.
#guard renderCasesModule "licence" "÷ 0020 ÷ 0020 ÷\t# x\n# EOF\n" matches
  .error "the file states no line count: its \"# Lines:\" trailer is missing"

-- A truncated file whose trailer was edited to agree must never render into the data the
-- theorem reads.
theorem «renderCasesModule refuses a test file whose trailer agrees with a count other than 853» :
    (match renderCasesModule
        "UNICODE LICENSE V3\n\nCopyright © 1991-2025 Unicode, Inc.\n"
        "÷ 0020 ÷ 0020 ÷\t# x\n#\n# Lines: 1\n#\n# EOF\n" with
      | .error _ => true
      | .ok _ => false) = true := by
  decide +kernel

-- Each case is written as its line and the expected clusters the file's markers give.
#guard renderCase (.ofClusters 840 [[0x61, 0x308], [0x62]]) ==
  "  .ofClusters 840 [[0x0061, 0x0308], [0x0062]]"

-- `ofClusters` gives the code points as the clusters joined, as the parser reads them.
#guard (GraphemeBreakCase.ofClusters 840 [[0x61, 0x308], [0x62]]).codePoints == [0x61, 0x308, 0x62]

/-! ## Comparing clusters -/

-- A segmenter that splits every code point apart gets both joined lines wrong, so both line
-- numbers must be reported, not only the first; the line in between is right and must not appear.
theorem «mismatches names every differing line, in file order» :
    (mismatches
        (fun cps => cps.map fun c => [c])
        [ { line := 30, codePoints := [0x000D, 0x000A], expected := [[0x000D, 0x000A]] },
          { line := 35, codePoints := [0x0020, 0x0020], expected := [[0x0020], [0x0020]] },
          { line := 40, codePoints := [0x1F1E6, 0x1F1E7], expected := [[0x1F1E6, 0x1F1E7]] } ]
      == [30, 40]) = true := by
  decide

-- Twelve differing lines is more than the ten that the existing table
-- comparison reports, so a copied cap would drop the last two.
theorem «mismatches names all twelve differing lines with no cap» :
    mismatches (fun cps => cps.map fun c => [c])
      ((List.range 12).map fun i =>
        ({ line := 100 + i, codePoints := [0x000D, 0x000A],
           expected := [[0x000D, 0x000A]] } : GraphemeBreakCase))
    = [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111] := by
  decide

-- A segmenter that drops the text must be caught on every line; only the line
-- it gets right (line 31) is left out, and lines keep the file's order.
theorem «mismatches reports a segmenter that returns no clusters» :
    mismatches (fun cps => if cps = [0x0020] then [[0x0020]] else [])
      [({ line := 29, codePoints := [0x000D, 0x000A], expected := [[0x000D, 0x000A]] } : GraphemeBreakCase),
       { line := 31, codePoints := [0x0020], expected := [[0x0020]] },
       { line := 640, codePoints := [0x1F1E6, 0x1F1E7], expected := [[0x1F1E6, 0x1F1E7]] }]
    = [29, 640] := by
  decide

-- A segmenter that keeps the whole input as one cluster agrees with lines whose expected
-- result is one cluster, so nothing is reported for them.
theorem «mismatches is empty when every line's clusters agree» :
    (mismatches
        (fun cps => [cps])
        [ { line := 29, codePoints := [0x000D, 0x000A], expected := [[0x000D, 0x000A]] },
          { line := 31, codePoints := [0x1F1E6, 0x1F1E7], expected := [[0x1F1E6, 0x1F1E7]] } ]
      == []) = true := by
  decide
