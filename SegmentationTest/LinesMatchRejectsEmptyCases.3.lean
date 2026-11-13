import SegmentationTest.GraphemeBreakTestTheorem

-- The decided check must count the cases: "matches every one of the 853 lines of
-- GraphemeBreakTest.txt", so zero lines with zero mismatches must not pass.
theorem «linesMatch is false for an empty case list, so a dropped data module cannot prove the theorem» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters [] = false := by
  decide +kernel
