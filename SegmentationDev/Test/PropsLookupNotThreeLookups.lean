import Segmentation

-- "Define `Segmentation.Tables.propsLookup (c : Char) : Segmentation.Props` as one lookup in it."
-- Defining `propsLookup` as `props` would make the equality theorem hold trivially while still
-- running three searches; this definitional check fails on that.
theorem «propsLookup is one lookup in the combined table, not the three lookups» :
    ∀ c : Char,
      Segmentation.Tables.propsLookup c =
        Segmentation.Tables.Range.lookup Segmentation.Tables.propsDefault
          Segmentation.Tables.propsRanges c.toNat :=
  fun _ => rfl
