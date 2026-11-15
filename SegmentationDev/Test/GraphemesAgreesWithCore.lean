import Segmentation

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷  (× [9.0], ÷ [999.0])
-- "The core works over `List Char`; the `String` functions are a thin layer through core's `String.toList` lemmas."
set_option maxRecDepth 20000 in
theorem graphemes_agrees_with_core_on_letter_with_mark_line_840 :
    (Segmentation.clustersOf Segmentation.Tables.props ['a', '\u0308', 'b'] == [['a', '\u0308'], ['b']]
      && Segmentation.graphemes "a\u0308b" == ["a\u0308", "b"]) = true := by
  decide
