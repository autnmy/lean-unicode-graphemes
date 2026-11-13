import SegmentationTest.GraphemeBreakTestTheorem

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt". An empty list has no mismatches, so only the count check can stop it.
theorem «linesMatch is false on an empty case list, so no embedded data proves nothing (R1)» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters [] = false := by
  decide +kernel
