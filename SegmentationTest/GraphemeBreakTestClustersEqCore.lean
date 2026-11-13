import SegmentationTest.GraphemeBreakTestTheorem

-- The kernel decides over the List Char core; this link must hold for every input, so it is a
-- proved lemma, not a per-input check.
theorem «clusters_eq_coreClusters ties graphemes to the core for every code point list» :
    ∀ cps : List Nat, SegmentationTest.GraphemeBreakTestLine.clusters cps
      = SegmentationTest.GraphemeBreakTestTheorem.coreClusters cps :=
  SegmentationTest.GraphemeBreakTestTheorem.clusters_eq_coreClusters
