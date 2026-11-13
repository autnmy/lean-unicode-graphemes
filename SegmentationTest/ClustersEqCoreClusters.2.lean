import SegmentationTest.GraphemeBreakTestTheorem

-- The kernel decides over the List Char core; this lemma is what makes the result a statement
-- about `graphemes`, so it must hold for every code point list, not only the tested ones.
theorem «clusters_eq_coreClusters ties the graphemes wrapper to the decided core for every input» :
    ∀ cps : List Nat, SegmentationTest.GraphemeBreakTestLine.clusters cps =
      SegmentationTest.GraphemeBreakTestTheorem.coreClusters cps :=
  SegmentationTest.GraphemeBreakTestTheorem.clusters_eq_coreClusters
