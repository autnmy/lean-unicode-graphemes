import SegmentationTest.GraphemeBreakTestTheorem

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt, proved by `decide +kernel` without `native_decide`, and CI checks it in
-- under 10 minutes; or the attempt is recorded as dropped because it cannot meet that limit."
-- The statement is pinned here, so a theorem about fewer lines or another function fails to match.
theorem «graphemes matches every one of the 853 lines of GraphemeBreakTest.txt» :
    SegmentationTest.GraphemeBreakTestData.cases.length = 853 ∧
      ∀ c ∈ SegmentationTest.GraphemeBreakTestData.cases,
        SegmentationTest.GraphemeBreakTestLine.clusters c.codePoints = c.expected :=
  SegmentationTest.GraphemeBreakTestTheorem.graphemes_match_graphemeBreakTest
