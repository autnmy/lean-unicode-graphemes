import SegmentationTest.GraphemeBreakTestData

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
-- The expected clusters come from the file's markers, not from the segmenter.
theorem «the embedded GraphemeBreakTest cases hold line 840 as the file writes it» :
    (SegmentationTest.GraphemeBreakTestData.cases.any fun c =>
      c.line == 840 && c.codePoints == [0x61, 0x308, 0x62]
        && c.expected == [[0x61, 0x308], [0x62]]) = true := by
  decide +kernel
