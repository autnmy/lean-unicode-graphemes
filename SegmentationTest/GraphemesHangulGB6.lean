import Segmentation

-- GraphemeBreakTest.txt line 447: ÷ 1100 × 1100 ÷  (× [6.0])
-- "the functions agree with UAX #29 on hand-picked lines of the committed test file `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, at least one line for each rule GB3 to GB13"
set_option maxRecDepth 20000 in
theorem «graphemes keeps two Hangul L jamo together by GB6 (GraphemeBreakTest.txt line 447)» :
    (Segmentation.graphemes "\u1100\u1100" == ["\u1100\u1100"]
      && Segmentation.boundaries "\u1100\u1100" == [0, 2]) = true := by
  decide
