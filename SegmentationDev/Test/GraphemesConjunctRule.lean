import SegmentationDev.Test.GraphemeBreakTestLine

open SegmentationDev.Test.GraphemeBreakTestLine

-- GB9c, on lines of data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt. The rule reads
-- Indic_Conjunct_Break, needs no consonant before the linker (revision 49), and joins only a
-- following InCB Consonant.

-- Line 179: ÷ 094D × 0915 ÷  (× [9.3]); a linker at the start of the text.
#guard clusters [0x094D, 0x0915] == [[0x094D, 0x0915]]
#guard cuts [0x094D, 0x0915] == [0, 2]

-- Line 180: ÷ 094D × 0308 × 0915 ÷  (× [9.0], × [9.3]); an InCB Extend after the linker.
#guard clusters [0x094D, 0x0308, 0x0915] == [[0x094D, 0x0308, 0x0915]]
#guard cuts [0x094D, 0x0308, 0x0915] == [0, 3]

-- Line 659: ÷ 1CF5 × 0915 ÷  (× [9.3]); a linker whose Grapheme_Cluster_Break is not Extend.
#guard clusters [0x1CF5, 0x0915] == [[0x1CF5, 0x0915]]
#guard cuts [0x1CF5, 0x0915] == [0, 2]

-- Line 852: ÷ 0915 × 094D × 0924 ÷  (× [9.0], × [9.3])
#guard clusters [0x0915, 0x094D, 0x0924] == [[0x0915, 0x094D, 0x0924]]
#guard cuts [0x0915, 0x094D, 0x0924] == [0, 3]

-- Line 858: ÷ 0915 × 094D ÷ 0061 ÷  (× [9.0], ÷ [999.0]); the next code point is no consonant.
#guard clusters [0x0915, 0x094D, 0x0061] == [[0x0915, 0x094D], [0x0061]]
#guard cuts [0x0915, 0x094D, 0x0061] == [0, 2, 3]

-- Line 658: ÷ 1CF5 × 0308 ÷ 1CF5 ÷  (× [9.0], ÷ [999.0]); a linker is not a consonant.
#guard clusters [0x1CF5, 0x0308, 0x1CF5] == [[0x1CF5, 0x0308], [0x1CF5]]
#guard cuts [0x1CF5, 0x0308, 0x1CF5] == [0, 2, 3]
