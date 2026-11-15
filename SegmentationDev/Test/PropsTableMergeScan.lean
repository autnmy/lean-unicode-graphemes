import SegmentationDev.Gate.Axioms
import Segmentation

-- "A kernel check over every code point is too slow, so prove it through a general lemma about
-- merging sorted range lists plus the existing facts in `Segmentation/RangeLookup.lean`
-- (`Range.lookup_eq_scan`, `Range.Sorted`) and `Segmentation/TableLookup.lean` (`*_sorted`,
-- `props_eq_scan`)."
-- The statement holds for every code point `n` and every pair of sorted lists of any value
-- types, so it covers overlaps, gaps and shared endpoints without sampling them.
theorem «mergeWith scans as the pair of scans for any two sorted range lists» :
    ∀ {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
      (a : List (Segmentation.Tables.Range α)) (b : List (Segmentation.Tables.Range β)) (n : Nat),
      Segmentation.Tables.Range.chainOK a = true →
      Segmentation.Tables.Range.chainOK b = true →
      Segmentation.Tables.Range.scanList (f da db) (Segmentation.Tables.Range.mergeWith f da db a b) n =
        f (Segmentation.Tables.Range.scanList da a n) (Segmentation.Tables.Range.scanList db b n) := by
  intro α β γ f da db a b n ha hb
  apply Segmentation.Tables.Range.scanList_mergeWith <;> assumption
