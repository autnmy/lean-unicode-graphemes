import Segmentation

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷  (× [9.0], ÷ [999.0])
-- "The core works over `List Char`; the `String` functions are a thin layer through core's `String.toList` lemmas."
set_option maxRecDepth 20000 in
theorem «graphemes and the List Char core give the same split of a letter with a mark (GraphemeBreakTest.txt line 840)» :
    (Segmentation.clustersOf Segmentation.Tables.props ['a', '\u0308', 'b'] == [['a', '\u0308'], ['b']]
      && Segmentation.graphemes "a\u0308b" == ["a\u0308", "b"]) = true := by
  decide
