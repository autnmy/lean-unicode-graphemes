import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile

-- D800 is a surrogate, not a valid Char. Char.ofNat would quietly turn it into U+0000, so the
-- parser must refuse it rather than test the segmenter on a different code point.
theorem «parseTestFile rejects a surrogate code point beside a valid line» :
    ((match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n" with
      | .ok cases => cases.length == 1
      | .error _ => false) &&
     (match parseTestFile "÷ 0041 ÷ 0042 ÷\t# ok\n÷ D800 ÷\t# bad\n" with
      | .ok _ => false
      | .error _ => true)) = true := by decide +kernel
