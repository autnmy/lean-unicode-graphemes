import Segmentation

-- GraphemeBreakTest.txt line 848: ÷ 0061 × 200D ÷ 1F6D1 ÷  (× [9.0], ÷ [999.0])
-- GB11 needs an Extended_Pictographic before the ZWJ; a letter there must not arm it.
set_option maxRecDepth 20000 in
theorem «graphemes does not join a pictograph after ZWJ that follows a letter (GraphemeBreakTest.txt line 848)» :
    (Segmentation.graphemes "\u0061\u200D🛑" == ["\u0061\u200D", "🛑"]) = true := by
  decide
