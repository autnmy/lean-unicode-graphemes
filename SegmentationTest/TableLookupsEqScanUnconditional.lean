import Segmentation

open Segmentation Segmentation.Tables in
-- "A theorem that the lookup used by `Tables.props` (for example a binary search over sorted
-- ranges) returns the same value as a linear scan of the same range list, for every code point."
-- The statements carry no hypothesis, so the sortedness of the real tables must be proved, not
-- left to callers.
theorem «gcbOf, extPictOf and incbOf equal the scan for every n with no sortedness premise» :
    (∀ n : Nat, gcbOf n = Range.scan .Other gcbRanges n) ∧
    (∀ n : Nat, extPictOf n = Range.scan false extPictRanges n) ∧
    (∀ n : Nat, incbOf n = Range.scan .None incbRanges n) :=
  ⟨gcbOf_eq_scan, extPictOf_eq_scan, incbOf_eq_scan⟩
