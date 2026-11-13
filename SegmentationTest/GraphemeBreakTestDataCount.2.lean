import SegmentationTest.GraphemeBreakTestData

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt"
theorem «the embedded GraphemeBreakTest.txt cases number exactly 853» :
    SegmentationTest.GraphemeBreakTestData.cases.length = 853 := by
  decide +kernel
