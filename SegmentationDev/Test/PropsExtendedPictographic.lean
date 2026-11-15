import Segmentation

-- U+00A9 is listed as Extended_Pictographic in emoji/emoji-data.txt; U+0041 is not.
set_option maxRecDepth 20000 in
theorem props_marks_00A9_pictographic_and_not_0041 :
    ((Segmentation.Tables.props '\u00A9').extPict, (Segmentation.Tables.props 'A').extPict)
      = (true, false) := by
  decide
