import SegmentationTest.GraphemeBreakTestTheorem

-- The kernel decides over the List Char core; this lemma is what makes that a statement about
-- `graphemes`, so it must hold for every input, not only the decided ones.
theorem «the graphemes wrapper and coreClusters agree on every code point list» :
    ∀ cps : List Nat, SegmentationTest.GraphemeBreakTestLine.clusters cps =
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters cps :=
  SegmentationTest.GraphemeBreakTestTheorem.clusters_eq_coreClusters
