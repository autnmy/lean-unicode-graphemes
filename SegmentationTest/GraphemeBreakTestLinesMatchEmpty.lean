import SegmentationTest.GraphemeBreakTestTheorem

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt": with no cases, no line is compared, so the check must say false.
theorem «linesMatch rejects an empty case list, so a missing file's data cannot prove the 853-line theorem» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters [] = false := by
  decide +kernel
