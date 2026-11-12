import Segmentation

-- GraphemeBreakProperty.txt spells the value `Regional_Indicator`; the type names it `GCB.RI`.
set_option maxRecDepth 20000 in
theorem «props maps Regional_Indicator U+1F1E6 to RI and U+200D to ZWJ» :
    ((Segmentation.Tables.props (Char.ofNat 0x1F1E6)).gcb == Segmentation.GCB.RI &&
     (Segmentation.Tables.props '\u200D').gcb == Segmentation.GCB.ZWJ &&
     (Segmentation.Tables.props '\u0300').gcb == Segmentation.GCB.Extend &&
     (Segmentation.Tables.props '\u0903').gcb == Segmentation.GCB.SpacingMark) = true := by
  decide
