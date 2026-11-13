import SegmentationTest.GraphemeBreakTestTheorem

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt". The full list passes the count check, so this fails only if the
-- cluster comparison itself catches the wrong segmenter.
set_option maxRecDepth 20000 in
theorem «linesMatch is false over all 853 embedded cases for a segmenter that never joins (R1)» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch
      (fun cps => cps.map ([·])) SegmentationTest.GraphemeBreakTestData.cases = false := by
  decide +kernel
