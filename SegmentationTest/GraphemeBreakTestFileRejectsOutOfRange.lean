import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile

-- 110000 is past the last Unicode code point, so it is not a valid Char and the line must fail.
theorem «parseTestFile rejects a code point above 10FFFF beside a valid line» :
    ((match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n" with
      | .ok cases => cases.length == 1
      | .error _ => false) &&
     (match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n÷ 110000 ÷\t# bad\n" with
      | .ok _ => false
      | .error _ => true)) = true := by decide +kernel
