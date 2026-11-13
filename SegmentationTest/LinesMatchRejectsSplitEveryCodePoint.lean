import SegmentationTest.GraphemeBreakTestTheorem

-- The full case list has the right count, so only the cluster comparison can make this false:
-- a check that ignored mismatches would prove the theorem for any segmenter.
set_option maxRecDepth 20000 in
theorem «linesMatch is false on all 853 cases for a segmenter that never joins code points» :
    SegmentationTest.GraphemeBreakTestTheorem.linesMatch (fun cps => cps.map ([·]))
      SegmentationTest.GraphemeBreakTestData.cases = false := by
  decide +kernel
