import SegmentationTest.GraphemeBreakTestFile

-- The issue: "fails naming every line whose clusters differ". A segmenter that splits every
-- code point apart gets both joined lines wrong, so both line numbers must be reported, not
-- only the first and not a capped few; the line in between is right and must not appear.
theorem «mismatches names every differing line, in file order» :
    (SegmentationTest.GraphemeBreakTestFile.mismatches
        (fun cps => cps.map fun c => [c])
        [ { line := 30, codePoints := [0x000D, 0x000A], expected := [[0x000D, 0x000A]] },
          { line := 35, codePoints := [0x0020, 0x0020], expected := [[0x0020], [0x0020]] },
          { line := 40, codePoints := [0x1F1E6, 0x1F1E7], expected := [[0x1F1E6, 0x1F1E7]] } ]
      == [30, 40]) = true := by
  decide
