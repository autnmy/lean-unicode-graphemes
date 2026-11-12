import SegmentationTest.GraphemeBreakTestFile

-- "`lake test` passes all 853 lines of the test file."
-- Only ÷ and × are markers; a "+" must fail the parse, not be read as either.
theorem «parseTestFile fails on an unknown marker beside a valid line» :
    (SegmentationTest.GraphemeBreakTestFile.parseTestFile
      "÷ 0020 ÷ 0020 ÷\t# ok\n÷ 0020 + 0020 ÷\t# bad marker\n").toBool = false := by
  decide
