import Segmentation

-- "Define `Segmentation.Tables.propsLookup (c : Char) : Segmentation.Props` as one lookup in it."
-- Holding by `rfl` rules out a definition that calls `props` or the three source tables.
open Segmentation.Tables in
theorem «propsLookup is one Range.lookup in the combined table» :
    ∀ c : Char, propsLookup c = Range.lookup propsDefault propsRanges c.toNat :=
  fun _ => rfl
