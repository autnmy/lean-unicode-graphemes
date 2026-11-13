import SegmentationTest.GraphemeBreakTestTheorem

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The count is right (853 cases), so only
-- the cluster comparison can make the check fail here.
set_option maxRecDepth 20000 in
theorem «linesMatch rejects 853 lines when a segmenter that never joins gets them wrong» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch (fun cps => cps.map ([·]))
      (List.replicate 853
        ({ line := 840, codePoints := [0x61, 0x308, 0x62], expected := [[0x61, 0x308], [0x62]] } :
          SegmentationTest.GraphemeBreakTestFile.GraphemeBreakCase)) = false := by
  decide +kernel
