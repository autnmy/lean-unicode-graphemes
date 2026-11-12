import Segmentation

-- GraphemeBreakTest.txt line 834: ÷ 1F1E6 × 1F1E7 ÷ 1F1E8 ÷ 0062 ÷  (× [12.0], ÷ [999.0], ÷ [999.0])
-- "the functions agree with UAX #29 on hand-picked lines of the committed test file `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, at least one line for each rule GB3 to GB13"
set_option maxRecDepth 20000 in
theorem «graphemes pairs regional indicators from the start of text by GB12 (GraphemeBreakTest.txt line 834)» :
    (Segmentation.graphemes "🇦🇧🇨b" == ["🇦🇧", "🇨", "b"]
      && Segmentation.boundaries "🇦🇧🇨b" == [0, 2, 3, 4]) = true := by
  decide
