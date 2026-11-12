import Segmentation

-- GraphemeBreakTest.txt line 29: ÷ 000D × 000A ÷  (× [3.0])
set_option maxRecDepth 20000 in
theorem «graphemes keeps CR LF together by GB3 (GraphemeBreakTest.txt line 29)» :
    (Segmentation.graphemes "\u000D\u000A" == ["\u000D\u000A"]) = true := by
  decide
