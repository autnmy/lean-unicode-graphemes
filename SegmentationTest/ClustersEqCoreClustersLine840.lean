import SegmentationTest.GraphemeBreakTestTheorem

-- GraphemeBreakTest.txt line 840: ÷ 0061 × 0308 ÷ 0062 ÷. The rewrite goes through the lemma,
-- so the result is about `graphemes`, while the kernel only evaluates the List Char core.
set_option maxRecDepth 20000 in
theorem «graphemes clusters a letter with a mark through the proved link to the core» :
    SegmentationTest.GraphemeBreakTestLine.clusters [0x61, 0x308, 0x62] = [[0x61, 0x308], [0x62]] := by
  rw [SegmentationTest.GraphemeBreakTestTheorem.clusters_eq_coreClusters]
  decide +kernel
