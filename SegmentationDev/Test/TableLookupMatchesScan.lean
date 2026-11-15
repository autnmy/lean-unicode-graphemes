import SegmentationDev.Gate.Axioms
import Segmentation

/-!
Checks of `Segmentation.TableLookup`: the committed tables pass `Range.Sorted`, and the lookups
`props` reads equal the linear scan of their tables for every code point, with no hypothesis.
-/

-- "Any lemmas about sorted, non-overlapping ranges the generated tables need, checked against
-- the tables themselves."
open Segmentation.Tables in
theorem committed_tables_sorted_and_non_overlapping :
    Range.Sorted gcbRanges ∧ Range.Sorted extPictRanges ∧ Range.Sorted incbRanges :=
  ⟨gcbRanges_sorted, extPictRanges_sorted, incbRanges_sorted⟩

open Segmentation Segmentation.Tables in
-- "A theorem that the lookup used by `Tables.props` (for example a binary search over sorted
-- ranges) returns the same value as a linear scan of the same range list, for every code point."
-- The statements carry no hypothesis, so the sortedness of the real tables must be proved, not
-- left to callers.
theorem gcbOf_extPictOf_incbOf_eq_scan_without_sorted_premise :
    (∀ n : Nat, gcbOf n = Range.scan .other gcbRanges n) ∧
    (∀ n : Nat, extPictOf n = Range.scan false extPictRanges n) ∧
    (∀ n : Nat, incbOf n = Range.scan .none incbRanges n) :=
  ⟨gcbOf_eq_scan, extPictOf_eq_scan, incbOf_eq_scan⟩

open Segmentation Segmentation.Tables in
theorem props_eq_linear_scan_of_tables_for_every_char :
    ∀ c : Char, props c =
      { gcb := Range.scan GCB.other gcbRanges c.toNat,
        extPict := Range.scan false extPictRanges c.toNat,
        incb := Range.scan InCB.none incbRanges c.toNat } :=
  props_eq_scan

-- The scan is evaluated directly, then carried back to the lookups through the corollaries, so
-- both the reference and the theorems must agree with the Unicode data values.
open Segmentation Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem linear_scan_of_committed_tables_gives_file_values_094D_00A9_10FFFF :
    incbOf 0x094D = InCB.linker ∧ extPictOf 0x00A9 = true ∧ extPictOf 0x0041 = false ∧
      incbOf 0x10FFFF = InCB.none := by
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
