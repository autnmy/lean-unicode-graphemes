import Segmentation

-- U+00A9 is listed as Extended_Pictographic in emoji/emoji-data.txt; U+0041 is not.
set_option maxRecDepth 20000 in
theorem «props marks U+00A9 Extended_Pictographic and leaves U+0041 unmarked» :
    ((Segmentation.Tables.props '\u00A9').extPict, (Segmentation.Tables.props 'A').extPict)
      = (true, false) := by
  decide
