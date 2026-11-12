import Segmentation

-- GraphemeBreakTest.txt line 28: ÷ 000D ÷ 0308 ÷ 000D ÷  (÷ [4.0], ÷ [5.0])
-- The mark after CR must not join it: GB4 comes before GB9 in the rule order.
set_option maxRecDepth 20000 in
theorem «graphemes applies GB4 and GB5 before GB9 (GraphemeBreakTest.txt line 28)» :
    (Segmentation.graphemes "\u000D\u0308\u000D" == ["\u000D", "\u0308", "\u000D"]) = true := by
  decide
