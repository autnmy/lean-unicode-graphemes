import Segmentation.Tables
import Segmentation.RangeLookup

/-!
# The property lookups agree with a linear scan

`Range.lookup_eq_scan` holds for any table that passes `Range.Sorted`. This module checks that
condition on the three generated tables, so the agreement holds for the lookups `props` reads,
for every code point and with no hypothesis left to callers.

The sortedness facts are proved by `decide`, which the kernel evaluates over the committed
tables. A regenerated table that is out of order or has overlapping ranges makes the build fail
here, rather than leaving the binary search wrong without notice.
-/

namespace Segmentation.Tables

-- The kernel walks every range of each table, and the tables are long lists, so the default
-- recursion depth is too small.
set_option maxRecDepth 20000 in
/-- `gcbRanges` is sorted by `lo` with no overlapping ranges. -/
theorem gcbRanges_sorted : Range.Sorted gcbRanges := by decide

set_option maxRecDepth 20000 in
/-- `extPictRanges` is sorted by `lo` with no overlapping ranges. -/
theorem extPictRanges_sorted : Range.Sorted extPictRanges := by decide

set_option maxRecDepth 20000 in
/-- `incbRanges` is sorted by `lo` with no overlapping ranges. -/
theorem incbRanges_sorted : Range.Sorted incbRanges := by decide

/-- `gcbOf` gives the value of the first range of `gcbRanges` that holds `n`, or `Other`. -/
theorem gcbOf_eq_scan (n : Nat) : gcbOf n = Range.scan .Other gcbRanges n :=
  Range.lookup_eq_scan gcbRanges_sorted n

/-- `extPictOf` gives the value of the first range of `extPictRanges` that holds `n`, or
`false`. -/
theorem extPictOf_eq_scan (n : Nat) : extPictOf n = Range.scan false extPictRanges n :=
  Range.lookup_eq_scan extPictRanges_sorted n

/-- `incbOf` gives the value of the first range of `incbRanges` that holds `n`, or `None`. -/
theorem incbOf_eq_scan (n : Nat) : incbOf n = Range.scan .None incbRanges n :=
  Range.lookup_eq_scan incbRanges_sorted n

/-- `props` reads each property of `c` as the linear scan of its table would. -/
theorem props_eq_scan (c : Char) :
    props c =
      { gcb := Range.scan .Other gcbRanges c.toNat,
        extPict := Range.scan false extPictRanges c.toNat,
        incb := Range.scan .None incbRanges c.toNat } := by
  simp only [props, gcbOf_eq_scan, extPictOf_eq_scan, incbOf_eq_scan]

end Segmentation.Tables
