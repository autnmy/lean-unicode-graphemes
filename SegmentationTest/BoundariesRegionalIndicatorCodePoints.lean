import Segmentation

-- "`Segmentation.boundaries : String → List Nat`, the cut positions counted in code points."
-- GraphemeBreakTest.txt line 835: ÷ 0061 ÷ 1F1E6 × 1F1E7 ÷ 1F1E8 ÷ 0062 ÷
-- Each RI takes four UTF-8 bytes, so a count in bytes gives different numbers.
set_option maxRecDepth 20000 in
theorem «boundaries counts code points not bytes on regional indicators (GraphemeBreakTest.txt line 835)» :
    (Segmentation.boundaries "\u0061🇦🇧🇨\u0062" == [0, 1, 3, 4, 5]) = true := by
  decide
