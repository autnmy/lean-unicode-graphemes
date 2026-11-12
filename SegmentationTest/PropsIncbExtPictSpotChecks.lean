import Segmentation

set_option maxRecDepth 20000 in
theorem «props reads InCB Linker for U+094D and Extended_Pictographic for U+00A9» :
    ((Segmentation.Tables.props '\u094D').incb == Segmentation.InCB.Linker &&
     (Segmentation.Tables.props '\u00A9').extPict == true &&
     (Segmentation.Tables.props '\u0041').extPict == false) = true := by
  decide
