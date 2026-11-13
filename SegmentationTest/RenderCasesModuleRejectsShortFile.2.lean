import SegmentationTest.GraphemeBreakTestFile

-- A truncated file whose trailer still says 853 must never render, or the embedded cases
-- would cover less than the whole file.
theorem «renderCasesModule refuses a file whose test lines do not number 853» :
    (SegmentationTest.GraphemeBreakTestFile.renderCasesModule "licence"
      "÷ 0020 ÷ 0020 ÷\t# x\n÷ 0061 × 0308 ÷\t# y\n#\n# Lines: 853\n#\n# EOF\n").toBool = false := by
  decide +kernel
