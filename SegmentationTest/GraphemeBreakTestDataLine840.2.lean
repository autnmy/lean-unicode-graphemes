import SegmentationTest.GraphemeBreakTestData

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
theorem «the embedded cases hold line 840 of GraphemeBreakTest.txt with the file's markers» :
    (SegmentationTest.GraphemeBreakTestData.cases.any fun c =>
      c.line == 840 && c.codePoints == [0x61, 0x308, 0x62]
        && c.expected == [[0x61, 0x308], [0x62]]) = true := by
  decide +kernel
