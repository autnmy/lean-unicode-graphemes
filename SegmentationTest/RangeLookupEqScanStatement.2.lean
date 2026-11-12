import Segmentation

-- The ascription pins the theorem to `Range.lookup` as the library defines it, for every
-- sorted table and every `n`, so a theorem about a copy of the search, or one bounded on `n`,
-- fails here.
theorem «lookup_eq_scan is stated for Range.lookup itself and every n» :
    ∀ {α : Type} (default : α) (table : Array (Segmentation.Tables.Range α)),
      Segmentation.Tables.Range.Sorted table → ∀ n : Nat,
        Segmentation.Tables.Range.lookup default table n
          = Segmentation.Tables.Range.scan default table n :=
  fun _ _ h n => Segmentation.Tables.Range.lookup_eq_scan h n
