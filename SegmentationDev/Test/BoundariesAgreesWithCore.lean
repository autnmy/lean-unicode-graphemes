import Segmentation

-- GraphemeBreakTest.txt line 832: ÷ AC00 × 11A8 ÷ 1100 ÷
-- "The core works over `List Char`; the `String` functions are a thin layer through core's `String.toList` lemmas."
set_option maxRecDepth 20000 in
theorem «boundaries and the List Char core give the same cuts for a Hangul syllable and jamo (GraphemeBreakTest.txt line 832)» :
    (Segmentation.cutsOf Segmentation.Tables.props ['\uAC00', '\u11A8', '\u1100'] == [0, 2, 3]
      && Segmentation.boundaries "\uAC00\u11A8\u1100" == [0, 2, 3]) = true := by
  decide
