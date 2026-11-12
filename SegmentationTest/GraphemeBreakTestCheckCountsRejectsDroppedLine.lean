import SegmentationTest.GraphemeBreakTestFile

-- The issue: "runs `Segmentation.graphemes` on each of its 853 test lines". A parser that
-- skipped one line must not pass, whether the file states 853 or the short count itself.
theorem «checkCounts rejects a parse that dropped a line» :
    ((match SegmentationTest.GraphemeBreakTestFile.checkCounts 852 (some 853) with
        | .ok _ => false
        | .error _ => true) &&
     (match SegmentationTest.GraphemeBreakTestFile.checkCounts 852 (some 852) with
        | .ok _ => false
        | .error _ => true)) = true := by
  decide
