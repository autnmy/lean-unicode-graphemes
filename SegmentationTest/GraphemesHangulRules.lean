import SegmentationTest.GraphemeBreakTestLine

open SegmentationTest.GraphemeBreakTestLine

-- GB6 to GB8, the Hangul syllable rules, on lines of
-- data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt.

-- Line 447: ÷ 1100 × 1100 ÷  (× [6.0])
#guard clusters [0x1100, 0x1100] == [[0x1100, 0x1100]]
#guard cuts [0x1100, 0x1100] == [0, 2]

-- Line 491: ÷ 1160 × 11A8 ÷  (× [7.0])
#guard cuts [0x1160, 0x11A8] == [0, 2]

-- Line 531: ÷ 11A8 × 11A8 ÷  (× [8.0])
#guard cuts [0x11A8, 0x11A8] == [0, 2]

-- Line 832: ÷ AC00 × 11A8 ÷ 1100 ÷  (× [7.0], ÷ [999.0])
#guard clusters [0xAC00, 0x11A8, 0x1100] == [[0xAC00, 0x11A8], [0x1100]]
#guard cuts [0xAC00, 0x11A8, 0x1100] == [0, 2, 3]

-- Line 833: ÷ AC01 × 11A8 ÷ 1100 ÷  (× [8.0], ÷ [999.0])
#guard clusters [0xAC01, 0x11A8, 0x1100] == [[0xAC01, 0x11A8], [0x1100]]
#guard cuts [0xAC01, 0x11A8, 0x1100] == [0, 2, 3]
