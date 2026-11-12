import SegmentationTest.GraphemeBreakTestFile

-- The issue: "`lake test` passes all 853 lines of the test file."
theorem «checkCounts accepts 853 parsed lines when the file states 853» :
    (match SegmentationTest.GraphemeBreakTestFile.checkCounts 853 (some 853) with
      | .ok _ => true
      | .error _ => false) = true := by
  decide
