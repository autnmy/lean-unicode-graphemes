import Segmentation

-- GraphemeBreakTest.txt line 841: ÷ 0061 × 0903 ÷ 0062 ÷  (× [9.1], ÷ [999.0])
-- "the functions agree with UAX #29 on hand-picked lines of the committed test file `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, at least one line for each rule GB3 to GB13"
set_option maxRecDepth 20000 in
theorem «graphemes joins a SpacingMark to the letter before it by GB9a (GraphemeBreakTest.txt line 841)» :
    (Segmentation.graphemes "a\u0903b" == ["a\u0903", "b"]
      && Segmentation.boundaries "a\u0903b" == [0, 2, 3]) = true := by
  decide
