import SegmentationTest.GraphemeBreakTestTheorem

-- Three regional indicators: the first two join (GB12), the third starts a new cluster. These code
-- points sit above U+FFFF, so they also check the Nat to Char conversion keeps them intact.
set_option maxRecDepth 20000 in
theorem «coreClusters pairs regional indicators above U+FFFF» :
    (SegmentationTest.GraphemeBreakTestTheorem.coreClusters [0x1F1E6, 0x1F1E7, 0x1F1E8]
      == [[0x1F1E6, 0x1F1E7], [0x1F1E8]]) = true := by
  decide +kernel
