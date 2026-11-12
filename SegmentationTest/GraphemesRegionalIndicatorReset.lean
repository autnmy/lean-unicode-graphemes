import Segmentation

-- GraphemeBreakTest.txt line 836: ÷ 0061 ÷ 1F1E6 × 1F1E7 × 200D ÷ 1F1E8 ÷ 0062 ÷
-- The ZWJ is not RI, so the run of RI before 1F1E8 is empty and GB12/GB13 do not join it.
set_option maxRecDepth 20000 in
theorem «graphemes restarts the regional indicator pairing after ZWJ (GraphemeBreakTest.txt line 836)» :
    (Segmentation.graphemes "\u0061🇦🇧\u200D🇨\u0062"
      == ["\u0061", "🇦🇧\u200D", "🇨", "\u0062"]) = true := by
  decide
