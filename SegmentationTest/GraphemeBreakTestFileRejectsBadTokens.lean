import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile

-- Each bad line sits after a valid one, so a failure comes from the bad line and not from an
-- empty result. The error names the bad line's number so a broken run says where to look.

/-- The valid first line of every input below. -/
def graphemeBreakTestValidLine : String := "÷ 0041 ÷ 0042 ÷\t# ok\n"

#guard (parseTestFile graphemeBreakTestValidLine).toBool

-- A line without its leading break marker.
#guard parseTestFile (graphemeBreakTestValidLine ++ "0041 × 0042 ÷\t# bad\n") matches
  .error "line 2 is not a GraphemeBreakTest.txt test line: 0041 × 0042 ÷"

-- A token that is not hexadecimal.
#guard parseTestFile (graphemeBreakTestValidLine ++ "# comment\n÷ 00ZZ ÷\t# bad\n") matches
  .error "line 3 is not a GraphemeBreakTest.txt test line: ÷ 00ZZ ÷"

-- Two markers in a row, so a code point is missing between them.
#guard !(parseTestFile (graphemeBreakTestValidLine ++ "÷ 0041 × ÷\t# bad\n")).toBool

-- A line holding only the break marker has no code point at all.
#guard !(parseTestFile (graphemeBreakTestValidLine ++ "÷\t# bad\n")).toBool

-- Comment-only and blank lines are not test lines, and line numbers count them.
#guard (parseTestFile ("# header\n\n#\n" ++ graphemeBreakTestValidLine ++ "# Lines: 1\n")).toOption.map
  (·.map (·.line)) == some [4]

-- Empty text holds no test lines; `checkCounts` is what makes that a failure.
#guard (parseTestFile "").toOption.map (·.length) == some 0
