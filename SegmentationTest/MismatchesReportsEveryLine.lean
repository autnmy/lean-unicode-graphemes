import SegmentationTest.GraphemeBreakTestFile

open SegmentationTest.GraphemeBreakTestFile in
-- "A `lake test` driver that reads `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, runs `Segmentation.graphemes` on each of its 853 test lines, and fails naming every line whose clusters differ."
-- Twelve differing lines is more than the ten that the existing table
-- comparison reports, so a copied cap would drop the last two.
theorem «mismatches names all twelve differing lines with no cap» :
    mismatches (fun cps => cps.map fun c => [c])
      ((List.range 12).map fun i =>
        ({ line := 100 + i, codePoints := [0x000D, 0x000A],
           expected := [[0x000D, 0x000A]] } : GraphemeBreakCase))
    = [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111] := by
  decide
