import Segmentation

-- "A theorem that the lookup used by `Tables.props` (for example a binary search over sorted
-- ranges) returns the same value as a linear scan of the same range list, for every code point."
theorem «gcbOf equals the linear scan of gcbRanges for every code point with no hypothesis» :
    ∀ n : Nat, Segmentation.Tables.gcbOf n =
      Segmentation.Tables.Range.scan Segmentation.GCB.Other Segmentation.Tables.gcbRanges n :=
  Segmentation.Tables.gcbOf_eq_scan
