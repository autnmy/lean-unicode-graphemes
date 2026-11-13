import SegmentationTest.GraphemeBreakTestData

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The expected clusters come from the
-- file's markers, so the embedded case must carry them as the file states them.
set_option maxRecDepth 20000 in
theorem «the embedded cases hold GraphemeBreakTest.txt line 840 with the file's markers» :
    (SegmentationTest.GraphemeBreakTestData.cases.any fun c =>
      c.line == 840 && c.codePoints == [0x61, 0x308, 0x62] &&
        c.expected == [[0x61, 0x308], [0x62]]) = true := by
  decide +kernel
