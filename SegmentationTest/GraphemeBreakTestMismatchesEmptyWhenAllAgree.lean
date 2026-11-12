import SegmentationTest.GraphemeBreakTestFile

-- A segmenter that keeps the whole input as one cluster agrees with lines whose expected
-- result is one cluster, so nothing is reported for them.
theorem «mismatches is empty when every line's clusters agree» :
    (SegmentationTest.GraphemeBreakTestFile.mismatches
        (fun cps => [cps])
        [ { line := 29, codePoints := [0x000D, 0x000A], expected := [[0x000D, 0x000A]] },
          { line := 31, codePoints := [0x1F1E6, 0x1F1E7], expected := [[0x1F1E6, 0x1F1E7]] } ]
      == []) = true := by
  decide
