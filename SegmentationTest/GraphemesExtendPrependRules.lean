import SegmentationTest.GraphemeBreakTestLine

open SegmentationTest.GraphemeBreakTestLine

-- GB9, GB9a and GB9b, on lines of data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt.

-- Line 840: ÷ 0061 × 0308 ÷ 0062 ÷  (× [9.0], ÷ [999.0])
#guard clusters [0x0061, 0x0308, 0x0062] == [[0x0061, 0x0308], [0x0062]]
#guard cuts [0x0061, 0x0308, 0x0062] == [0, 2, 3]

-- Line 841: ÷ 0061 × 0903 ÷ 0062 ÷  (× [9.1], ÷ [999.0])
#guard clusters [0x0061, 0x0903, 0x0062] == [[0x0061, 0x0903], [0x0062]]
#guard cuts [0x0061, 0x0903, 0x0062] == [0, 2, 3]

-- Line 842: ÷ 0061 ÷ 0600 × 0062 ÷  (÷ [999.0], × [9.2])
#guard clusters [0x0061, 0x0600, 0x0062] == [[0x0061], [0x0600, 0x0062]]
#guard cuts [0x0061, 0x0600, 0x0062] == [0, 1, 3]

-- Line 361: ÷ 06DD × 1F1E6 ÷  (× [9.2]); a Prepend joins even a regional indicator.
#guard cuts [0x06DD, 0x1F1E6] == [0, 2]
