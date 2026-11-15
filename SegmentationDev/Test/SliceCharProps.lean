import Segmentation

-- "ASCII bytes are read without a table lookup and each non-ASCII code point does one lookup in
-- the combined table."
-- Both branches must still give the properties `Tables.props` gives. U+0023, U+002A and U+0030 are
-- emoji-related ASCII code points a hand-written table can get wrong; U+007F and U+0080 sit on
-- either side of the ASCII bound; the rest are non-ASCII code points with non-default properties.
set_option maxRecDepth 20000 in
theorem «charProps_equals_props_on_ascii_emoji_digits_and_non_ascii_code_points» :
    ([0x00, 0x0A, 0x0D, 0x23, 0x2A, 0x30, 0x39, 0x41, 0x7F, 0x80, 0x0301, 0x094D, 0x0915,
        0x200D, 0x1F1E6, 0x1F600, 0x10FFFF].all fun n =>
      decide (Segmentation.charProps (Char.ofNat n) = Segmentation.Tables.props (Char.ofNat n)))
      = true := by
  decide
