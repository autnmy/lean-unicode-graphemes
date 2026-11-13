import SegmentationTest.GraphemeBreakTestTheorem

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷, repeated to the file's 853 lines.
set_option maxRecDepth 20000 in
theorem «linesMatch accepts 853 correct lines segmented by coreClusters» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters
      (List.replicate 853
        ({ line := 840, codePoints := [0x61, 0x308, 0x62], expected := [[0x61, 0x308], [0x62]] } :
          SegmentationTest.GraphemeBreakTestFile.GraphemeBreakCase)) = true := by
  decide +kernel
