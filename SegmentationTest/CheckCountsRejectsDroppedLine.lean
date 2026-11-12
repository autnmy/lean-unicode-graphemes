import SegmentationTest.GraphemeBreakTestFile

-- "`lake test` passes all 853 lines of the test file."
-- A parser that silently skips one line must not pass: 852 parsed against a
-- stated 853 is a failure, and so is an empty parse against an empty trailer.
theorem «checkCounts rejects a parse that dropped a line the file states» :
    (SegmentationTest.GraphemeBreakTestFile.checkCounts 852 (some 853)).toBool = false ∧
    (SegmentationTest.GraphemeBreakTestFile.checkCounts 0 (some 0)).toBool = false ∧
    (SegmentationTest.GraphemeBreakTestFile.checkCounts 853 (some 853)).toBool = true := by
  decide
