import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile

-- Every line of the file ends with ÷ (the break at the end of the text). A line without it has
-- no defined last cluster, so it must fail instead of being guessed at or skipped.
theorem «parseTestFile rejects a line without its trailing break marker beside a valid line» :
    ((match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n" with
      | .ok cases => cases.length == 1
      | .error _ => false) &&
     (match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n÷ 0041 × 0042\t# bad\n" with
      | .ok _ => false
      | .error _ => true)) = true := by decide +kernel
