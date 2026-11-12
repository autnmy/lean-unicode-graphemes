import SegmentationTest.GraphemeBreakTestFile

-- "`lake test` passes all 853 lines of the test file."
-- Without the file's own "# Lines:" trailer there is nothing independent to
-- check the parsed count against, so the check must fail rather than pass.
theorem «checkCounts rejects 853 parsed lines when the file states no count» :
    (SegmentationTest.GraphemeBreakTestFile.checkCounts 853 none).toBool = false := by
  decide
