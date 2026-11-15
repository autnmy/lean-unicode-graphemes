import Segmentation

-- "Define `Segmentation.Tables.propsLookup (c : Char) : Segmentation.Props` as one lookup in it."
-- Holding by `rfl` pins the definition to a single binary search over the combined table, so a
-- definition that calls `props` or the three source tables fails here.
open Segmentation.Tables in
theorem «propsLookup_is_one_lookup_in_propsRanges» :
    ∀ c : Char, propsLookup c = Range.lookup propsDefault propsRanges c.toNat :=
  fun _ => rfl
