import SegmentationTest.GraphemeBreakTestFile

-- The expected clusters come from the file's ÷ and × markers, never from the segmenter.
-- The comment line is not a test line, so the data line is physical line 2.
theorem «parseTestFile reads expected clusters from the markers, astral code points included» :
    (match SegmentationTest.GraphemeBreakTestFile.parseTestFile
        "# header\n÷ 1F1E6 × 1F1E7 ÷ 0020 ÷\t# x\n" with
      | .ok [c] =>
        c.line == 2 && c.codePoints == [0x1F1E6, 0x1F1E7, 0x0020] &&
          c.expected == [[0x1F1E6, 0x1F1E7], [0x0020]]
      | _ => false) = true := by
  decide
