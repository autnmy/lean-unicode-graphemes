import Segmentation

-- GraphemeBreakTest.txt line 658: ÷ 1CF5 × 0308 ÷ 1CF5 ÷  (× [9.0], ÷ [999.0])
-- 1CF5 is an InCB Linker whose GCB is not Extend; a second linker is not a consonant, so GB9c does not apply.
set_option maxRecDepth 20000 in
theorem «graphemes breaks after a linker when no consonant follows (GraphemeBreakTest.txt line 658)» :
    (Segmentation.graphemes "\u1CF5\u0308\u1CF5" == ["\u1CF5\u0308", "\u1CF5"]) = true := by
  decide
