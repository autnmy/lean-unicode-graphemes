import SegmentationTest.GraphemeBreakTestTheorem

-- Three regional indicators (U+1F1E6 U+1F1E7 U+1F1E8): GB12/GB13 join the first two and break
-- before the third. Astral code points pass through Char.ofNat and back as numbers.
set_option maxRecDepth 20000 in
theorem «coreClusters pairs astral regional indicators into one flag cluster» :
    SegmentationTest.GraphemeBreakTestTheorem.coreClusters [0x1F1E6, 0x1F1E7, 0x1F1E8]
      = [[0x1F1E6, 0x1F1E7], [0x1F1E8]] := by
  decide +kernel
