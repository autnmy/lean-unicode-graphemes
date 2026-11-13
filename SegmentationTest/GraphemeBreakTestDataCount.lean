import SegmentationTest.GraphemeBreakTestData

theorem «the embedded GraphemeBreakTest.txt cases number exactly 853» :
    (SegmentationTest.GraphemeBreakTestData.cases.length ==
      SegmentationTest.GraphemeBreakTestFile.expectedLineCount) = true := by
  decide +kernel
