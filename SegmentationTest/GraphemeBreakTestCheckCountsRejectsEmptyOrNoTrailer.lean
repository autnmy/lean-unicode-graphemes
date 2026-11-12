import SegmentationTest.GraphemeBreakTestFile

-- A run that compared nothing, or a file with no "# Lines:" trailer, must fail rather than
-- pass with zero mismatches.
theorem «checkCounts rejects an empty parse and a missing trailer» :
    ((match SegmentationTest.GraphemeBreakTestFile.checkCounts 0 (some 0) with
        | .ok _ => false
        | .error _ => true) &&
     (match SegmentationTest.GraphemeBreakTestFile.checkCounts 853 none with
        | .ok _ => false
        | .error _ => true)) = true := by
  decide
