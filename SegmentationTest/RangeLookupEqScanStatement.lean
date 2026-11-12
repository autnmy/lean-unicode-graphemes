import Segmentation

-- The ascription pins the theorem to `Range.lookup` itself, as `Tables.props` calls it, so a
-- theorem about a different search, or one with an extra hypothesis, fails here.
theorem «lookup_eq_scan states that Range.lookup equals Range.scan on every sorted table for every n»
    {α : Type} {d : α} {table : Array (Segmentation.Tables.Range α)}
    (h : Segmentation.Tables.Range.Sorted table) (n : Nat) :
    Segmentation.Tables.Range.lookup d table n = Segmentation.Tables.Range.scan d table n :=
  Segmentation.Tables.Range.lookup_eq_scan h n
