import Segmentation

-- GraphemeBreakTest.txt line 846: ÷ 1F476 × 1F3FF × 0308 × 200D × 1F476 × 1F3FF ÷  (× [11.0] at the second 1F476)
set_option maxRecDepth 20000 in
theorem «graphemes joins pictographs across Extend and ZWJ by GB11 (GraphemeBreakTest.txt line 846)» :
    (Segmentation.graphemes "👶🏿\u0308\u200D👶🏿"
      == ["👶🏿\u0308\u200D👶🏿"]) = true := by
  decide
