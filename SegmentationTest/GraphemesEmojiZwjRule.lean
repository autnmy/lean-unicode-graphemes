import SegmentationTest.GraphemeBreakTestLine

open SegmentationTest.GraphemeBreakTestLine

-- GB11, on lines of data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt.

-- Line 846: ÷ 1F476 × 1F3FF × 0308 × 200D × 1F476 × 1F3FF ÷  (× [9.0] three times, × [11.0],
-- × [9.0]); GCB Extend code points between the pictograph and the ZWJ.
#guard clusters [0x1F476, 0x1F3FF, 0x0308, 0x200D, 0x1F476, 0x1F3FF] ==
  [[0x1F476, 0x1F3FF, 0x0308, 0x200D, 0x1F476, 0x1F3FF]]
#guard cuts [0x1F476, 0x1F3FF, 0x0308, 0x200D, 0x1F476, 0x1F3FF] == [0, 6]

-- Line 847: ÷ 1F6D1 × 200D × 1F6D1 ÷  (× [9.0], × [11.0])
#guard clusters [0x1F6D1, 0x200D, 0x1F6D1] == [[0x1F6D1, 0x200D, 0x1F6D1]]
#guard cuts [0x1F6D1, 0x200D, 0x1F6D1] == [0, 3]

-- Line 848: ÷ 0061 × 200D ÷ 1F6D1 ÷  (× [9.0], ÷ [999.0]); no pictograph before the ZWJ.
#guard clusters [0x0061, 0x200D, 0x1F6D1] == [[0x0061, 0x200D], [0x1F6D1]]
#guard cuts [0x0061, 0x200D, 0x1F6D1] == [0, 2, 3]
