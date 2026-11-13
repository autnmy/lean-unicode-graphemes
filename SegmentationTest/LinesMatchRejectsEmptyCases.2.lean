import SegmentationTest.GraphemeBreakTestTheorem

-- The decided check must count the lines: an empty list has no mismatches, so a check without the
-- count would accept it and the theorem would prove nothing about the 853 lines.
theorem «linesMatch rejects an empty case list because it does not hold 853 lines» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters [] = false := by
  decide +kernel
