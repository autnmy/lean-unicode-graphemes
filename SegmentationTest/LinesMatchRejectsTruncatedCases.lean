import SegmentationTest.GraphemeBreakTestTheorem

-- "The repository has a theorem stating that `graphemes` matches every one of the 853 lines of
-- GraphemeBreakTest.txt". The segmenter here answers each kept line with the file's own expected
-- clusters, so the only thing wrong is that 852 lines are missing.
theorem «linesMatch is false on a truncated case list even when every kept case matches (R1)» :
    (let kept := SegmentationTest.GraphemeBreakTestData.cases.take 1
     SegmentationTest.GraphemeBreakTestTheorem.linesMatch
       (fun cps => match kept.find? (fun c => c.codePoints == cps) with
         | some c => c.expected
         | none => [])
       kept) = false := by
  decide +kernel
