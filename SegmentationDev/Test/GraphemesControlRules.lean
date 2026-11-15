import SegmentationDev.Test.GraphemeBreakTestLine

open SegmentationDev.Test.GraphemeBreakTestLine

-- GB3 to GB5, on lines of data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt. Lines 28, 46 and
-- 748 also check that GB4 and GB5 win over the later rules GB9 and GB9a.

-- Line 29: ÷ 000D × 000A ÷  (× [3.0])
#guard clusters [0x000D, 0x000A] == [[0x000D, 0x000A]]
#guard cuts [0x000D, 0x000A] == [0, 2]

-- Line 28: ÷ 000D ÷ 0308 ÷ 000D ÷  (÷ [4.0], ÷ [5.0])
#guard clusters [0x000D, 0x0308, 0x000D] == [[0x000D], [0x0308], [0x000D]]
#guard cuts [0x000D, 0x0308, 0x000D] == [0, 1, 2, 3]

-- Line 46: ÷ 000D ÷ 0308 × 0903 ÷  (÷ [4.0], × [9.1])
#guard clusters [0x000D, 0x0308, 0x0903] == [[0x000D], [0x0308, 0x0903]]
#guard cuts [0x000D, 0x0308, 0x0903] == [0, 1, 3]

-- Line 748: ÷ 0020 × 0308 ÷ 000D ÷  (× [9.0], ÷ [5.0])
#guard clusters [0x0020, 0x0308, 0x000D] == [[0x0020, 0x0308], [0x000D]]
#guard cuts [0x0020, 0x0308, 0x000D] == [0, 2, 3]
