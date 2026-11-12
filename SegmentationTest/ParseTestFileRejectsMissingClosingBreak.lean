import SegmentationTest.GraphemeBreakTestFile

-- "`lake test` passes all 853 lines of the test file."
-- A line that cannot be read must fail the whole parse, never be skipped: the
-- valid first line makes sure the failure is not just an empty result.
theorem «parseTestFile fails on a line missing its closing break beside a valid line» :
    (SegmentationTest.GraphemeBreakTestFile.parseTestFile
      "÷ 0020 ÷ 0020 ÷\t# ok\n÷ 000D × 000A\t# no closing break\n").toBool = false := by
  decide
