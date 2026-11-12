import Segmentation

-- GraphemeBreakTest.txt line 842: ÷ 0061 ÷ 0600 × 0062 ÷  (÷ [999.0], × [9.2])
-- "the functions agree with UAX #29 on hand-picked lines of the committed test file `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, at least one line for each rule GB3 to GB13"
set_option maxRecDepth 20000 in
theorem «graphemes joins a Prepend to the letter after it by GB9b (GraphemeBreakTest.txt line 842)» :
    (Segmentation.graphemes "a\u0600b" == ["a", "\u0600b"]
      && Segmentation.boundaries "a\u0600b" == [0, 1, 3]) = true := by
  decide
