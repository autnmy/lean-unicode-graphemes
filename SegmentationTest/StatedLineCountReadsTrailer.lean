import SegmentationTest.GraphemeBreakTestFile

-- "runs `Segmentation.graphemes` on each of its 853 test lines": the count the
-- file states in its own trailer is what the parsed count is checked against.
theorem «statedLineCount reads 853 from the file's Lines trailer» :
    (SegmentationTest.GraphemeBreakTestFile.statedLineCount
        "÷ 0020 ÷ 0020 ÷\t# x\n#\n# Lines: 853\n#\n# EOF\n" == some 853 &&
      SegmentationTest.GraphemeBreakTestFile.statedLineCount
        "÷ 0020 ÷ 0020 ÷\t# x\n# EOF\n" == none) = true := by
  decide
