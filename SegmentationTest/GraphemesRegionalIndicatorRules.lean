import SegmentationTest.GraphemeBreakTestLine

open SegmentationTest.GraphemeBreakTestLine

-- GB12 and GB13, on lines of data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt. Regional
-- indicators join in pairs, counted from the start of their run; any other code point, a ZWJ
-- included, ends the run.

-- Line 321: ÷ 1F1E6 × 1F1E6 ÷  (× [12.0])
#guard clusters [0x1F1E6, 0x1F1E6] == [[0x1F1E6, 0x1F1E6]]
#guard cuts [0x1F1E6, 0x1F1E6] == [0, 2]

-- Line 834: ÷ 1F1E6 × 1F1E7 ÷ 1F1E8 ÷ 0062 ÷  (× [12.0], ÷ [999.0], ÷ [999.0])
#guard clusters [0x1F1E6, 0x1F1E7, 0x1F1E8, 0x0062] == [[0x1F1E6, 0x1F1E7], [0x1F1E8], [0x0062]]
#guard cuts [0x1F1E6, 0x1F1E7, 0x1F1E8, 0x0062] == [0, 2, 3, 4]

-- Line 835: ÷ 0061 ÷ 1F1E6 × 1F1E7 ÷ 1F1E8 ÷ 0062 ÷  (× [13.0])
#guard clusters [0x0061, 0x1F1E6, 0x1F1E7, 0x1F1E8, 0x0062] ==
  [[0x0061], [0x1F1E6, 0x1F1E7], [0x1F1E8], [0x0062]]
#guard cuts [0x0061, 0x1F1E6, 0x1F1E7, 0x1F1E8, 0x0062] == [0, 1, 3, 4, 5]

-- Line 836: ÷ 0061 ÷ 1F1E6 × 1F1E7 × 200D ÷ 1F1E8 ÷ 0062 ÷  (× [13.0], × [9.0], ÷ [999.0])
#guard clusters [0x0061, 0x1F1E6, 0x1F1E7, 0x200D, 0x1F1E8, 0x0062] ==
  [[0x0061], [0x1F1E6, 0x1F1E7, 0x200D], [0x1F1E8], [0x0062]]
#guard cuts [0x0061, 0x1F1E6, 0x1F1E7, 0x200D, 0x1F1E8, 0x0062] == [0, 1, 4, 5, 6]

-- Line 837: ÷ 0061 ÷ 1F1E6 × 200D ÷ 1F1E7 × 1F1E8 ÷ 0062 ÷  (× [9.0], ÷ [999.0], × [13.0])
#guard clusters [0x0061, 0x1F1E6, 0x200D, 0x1F1E7, 0x1F1E8, 0x0062] ==
  [[0x0061], [0x1F1E6, 0x200D], [0x1F1E7, 0x1F1E8], [0x0062]]
#guard cuts [0x0061, 0x1F1E6, 0x200D, 0x1F1E7, 0x1F1E8, 0x0062] == [0, 1, 3, 5, 6]

-- Line 838: ÷ 0061 ÷ 1F1E6 × 1F1E7 ÷ 1F1E8 × 1F1E9 ÷ 0062 ÷  (× [13.0] twice)
#guard clusters [0x0061, 0x1F1E6, 0x1F1E7, 0x1F1E8, 0x1F1E9, 0x0062] ==
  [[0x0061], [0x1F1E6, 0x1F1E7], [0x1F1E8, 0x1F1E9], [0x0062]]
#guard cuts [0x0061, 0x1F1E6, 0x1F1E7, 0x1F1E8, 0x1F1E9, 0x0062] == [0, 1, 3, 5, 6]
