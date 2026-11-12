import SegmentationTest.GraphemeBreakTestFile

-- "`lake test` passes all 853 lines of the test file."
-- A file cut to 852 lines whose trailer was edited to agree must still fail:
-- agreeing with the trailer alone is not enough, the count must be 853.
theorem «checkCounts rejects a file truncated with a matching trailer» :
    (SegmentationTest.GraphemeBreakTestFile.checkCounts 852 (some 852)).toBool = false := by
  decide
