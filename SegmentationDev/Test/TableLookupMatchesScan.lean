import SegmentationDev.Gate.Axioms
import Segmentation

/-!
Checks of `Segmentation.TableLookup`: the committed tables pass `Range.Sorted`, and the lookups
`props` reads equal the linear scan of their tables for every code point, with no hypothesis.
-/

-- "Any lemmas about sorted, non-overlapping ranges the generated tables need, checked against
-- the tables themselves."
open Segmentation.Tables in
theorem «the three committed tables are proved sorted and non-overlapping» :
    Range.Sorted gcbRanges ∧ Range.Sorted extPictRanges ∧ Range.Sorted incbRanges :=
  ⟨gcbRanges_sorted, extPictRanges_sorted, incbRanges_sorted⟩

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

open Segmentation Segmentation.Tables in
theorem «props reads every property through the linear scan of its table for every Char» :
    ∀ c : Char, props c =
      { gcb := Range.scan GCB.Other gcbRanges c.toNat,
        extPict := Range.scan false extPictRanges c.toNat,
        incb := Range.scan InCB.None incbRanges c.toNat } :=
  props_eq_scan

-- The scan is evaluated directly, then carried back to the lookups through the corollaries, so
-- both the reference and the theorems must agree with the Unicode data values.
open Segmentation Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «the linear scan of the committed tables gives the file values for U+094D, U+00A9 and U+10FFFF» :
    incbOf 0x094D = InCB.Linker ∧ extPictOf 0x00A9 = true ∧ extPictOf 0x0041 = false ∧
      incbOf 0x10FFFF = InCB.None := by
  rw [incbOf_eq_scan, incbOf_eq_scan, extPictOf_eq_scan, extPictOf_eq_scan]
  decide

-- "The theorem is proved with no `sorry`, and `#print axioms` shows nothing beyond the three
-- standard axioms." A proof by `sorry` depends on `sorryAx`, and one by `native_decide` on an
-- axiom that tactic adds, so either fails here.
#assert_axioms Segmentation.Tables.Range.lookup_eq_scan
  Segmentation.Tables.gcbRanges_sorted Segmentation.Tables.extPictRanges_sorted
  Segmentation.Tables.incbRanges_sorted Segmentation.Tables.gcbOf_eq_scan
  Segmentation.Tables.extPictOf_eq_scan Segmentation.Tables.incbOf_eq_scan
  Segmentation.Tables.props_eq_scan
