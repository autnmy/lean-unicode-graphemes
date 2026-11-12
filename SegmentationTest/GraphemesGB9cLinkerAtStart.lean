import Segmentation

-- GraphemeBreakTest.txt line 180: ÷ 094D × 0308 × 0915 ÷  (× [9.0], × [9.3])
-- No consonant comes before the linker, and an InCB Extend sits between linker and consonant.
set_option maxRecDepth 20000 in
theorem «graphemes joins a linker at the start of text to a consonant by GB9c (GraphemeBreakTest.txt line 180)» :
    (Segmentation.graphemes "\u094D\u0308\u0915" == ["\u094D\u0308\u0915"]) = true := by
  decide
