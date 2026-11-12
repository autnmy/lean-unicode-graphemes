import Segmentation

theorem «incbOf equals the linear scan of incbRanges for every code point with no hypothesis» :
    ∀ n : Nat, Segmentation.Tables.incbOf n =
      Segmentation.Tables.Range.scan Segmentation.InCB.None Segmentation.Tables.incbRanges n :=
  Segmentation.Tables.incbOf_eq_scan
