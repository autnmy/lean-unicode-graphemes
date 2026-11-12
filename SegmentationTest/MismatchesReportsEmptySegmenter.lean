import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile in
-- "fails naming every line whose clusters differ"
-- A segmenter that drops the text must be caught on every line; only the line
-- it gets right (line 31) is left out, and lines keep the file's order.
theorem «mismatches reports a segmenter that returns no clusters» :
    mismatches (fun cps => if cps = [0x0020] then [[0x0020]] else [])
      [({ line := 29, codePoints := [0x000D, 0x000A], expected := [[0x000D, 0x000A]] } : GraphemeBreakCase),
       { line := 31, codePoints := [0x0020], expected := [[0x0020]] },
       { line := 640, codePoints := [0x1F1E6, 0x1F1E7], expected := [[0x1F1E6, 0x1F1E7]] }]
    = [29, 640] := by
  decide
