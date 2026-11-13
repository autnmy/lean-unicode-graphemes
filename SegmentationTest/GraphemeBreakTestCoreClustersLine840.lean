import SegmentationTest.GraphemeBreakTestTheorem

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷
set_option maxRecDepth 20000 in
theorem «coreClusters joins a letter with its combining mark (GraphemeBreakTest.txt line 840)» :
    SegmentationTest.GraphemeBreakTestTheorem.coreClusters [0x61, 0x308, 0x62]
      = [[0x61, 0x308], [0x62]] := by
  decide +kernel
