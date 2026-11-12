import Segmentation

theorem «extPictOf equals the linear scan of extPictRanges for every code point with no hypothesis» :
    ∀ n : Nat, Segmentation.Tables.extPictOf n =
      Segmentation.Tables.Range.scan false Segmentation.Tables.extPictRanges n :=
  Segmentation.Tables.extPictOf_eq_scan
