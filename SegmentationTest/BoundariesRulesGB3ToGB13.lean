import Segmentation

-- "the functions agree with UAX #29 on hand-picked lines of the committed test file `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`, at least one line for each rule GB3 to GB13"
-- Lines: 29 (GB3), 28 (GB4, GB5), 46 (GB4 before GB9a), 447 (GB6), 491 (GB7), 531 (GB8),
-- 840 (GB9), 841 (GB9a), 361 (GB9b), 659 (GB9c), 847 (GB11), 321 (GB12), 838 (GB13).
set_option maxRecDepth 20000 in
theorem «boundaries agrees with GraphemeBreakTest.txt on one line for each rule GB3 to GB13» :
    (Segmentation.boundaries "\u000D\u000A" == [0, 2]
      && Segmentation.boundaries "\u000D\u0308\u000D" == [0, 1, 2, 3]
      && Segmentation.boundaries "\u000D\u0308\u0903" == [0, 1, 3]
      && Segmentation.boundaries "\u1100\u1100" == [0, 2]
      && Segmentation.boundaries "\u1160\u11A8" == [0, 2]
      && Segmentation.boundaries "\u11A8\u11A8" == [0, 2]
      && Segmentation.boundaries "a\u0308b" == [0, 2, 3]
      && Segmentation.boundaries "a\u0903b" == [0, 2, 3]
      && Segmentation.boundaries "\u06DD🇦" == [0, 2]
      && Segmentation.boundaries "\u1CF5\u0915" == [0, 2]
      && Segmentation.boundaries "🛑\u200D🛑" == [0, 3]
      && Segmentation.boundaries "🇦🇦" == [0, 2]
      && Segmentation.boundaries "a🇦🇧🇨🇩b" == [0, 1, 3, 5, 6]) = true := by
  decide
