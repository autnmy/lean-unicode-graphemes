import Segmentation

-- GraphemeBreakTest.txt line 832: ÷ AC00 × 11A8 ÷ 1100 ÷  (× [7.0], ÷ [999.0])
-- "the functions agree with UAX #29 on hand-picked lines of the committed test file `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, at least one line for each rule GB3 to GB13"
set_option maxRecDepth 20000 in
theorem «graphemes joins LV and T by GB7 then breaks before L (GraphemeBreakTest.txt line 832)» :
    (Segmentation.graphemes "\uAC00\u11A8\u1100" == ["\uAC00\u11A8", "\u1100"]
      && Segmentation.boundaries "\uAC00\u11A8\u1100" == [0, 2, 3]) = true := by
  decide
