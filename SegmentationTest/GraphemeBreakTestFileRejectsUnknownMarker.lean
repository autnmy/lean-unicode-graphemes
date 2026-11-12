import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile

-- The valid line alone parses, so the failure below comes from the "+" marker and not from an
-- empty or unreadable input. A skipped bad line would let the conformance run check less than
-- the whole file.
theorem «parseTestFile rejects a line with an unknown marker beside a valid line» :
    ((match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n" with
      | .ok cases => cases.length == 1
      | .error _ => false) &&
     (match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n÷ 0041 + 0042 ÷\t# bad\n" with
      | .ok _ => false
      | .error _ => true)) = true := by decide +kernel
