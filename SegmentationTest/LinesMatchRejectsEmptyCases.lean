import SegmentationTest.GraphemeBreakTestTheorem

-- An empty or truncated list has no mismatching line, so only the count check stops it proving.
theorem «linesMatch rejects an empty case list because it holds fewer than 853 lines» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters [] = false := by
  decide +kernel
