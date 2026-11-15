import SegmentationDev.Gate.Axioms
import Segmentation

-- "A kernel check over every code point is too slow, so prove it through a general lemma about
-- merging sorted range lists plus the existing facts in `Segmentation/RangeLookup.lean`
-- (`Range.lookup_eq_scan`, `Range.Sorted`) and `Segmentation/TableLookup.lean` (`*_sorted`,
-- `props_eq_scan`)."
-- The statement quantifies over every value type and every pair of sorted lists, so a lemma
-- proved only for the three concrete tables does not satisfy it.
theorem «mergeWith keeps any two sorted range lists sorted» :
    ∀ {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
      (a : List (Segmentation.Tables.Range α)) (b : List (Segmentation.Tables.Range β)),
      Segmentation.Tables.Range.chainOK a = true →
      Segmentation.Tables.Range.chainOK b = true →
      Segmentation.Tables.Range.chainOK (Segmentation.Tables.Range.mergeWith f da db a b) = true := by
  intro α β γ f da db a b ha hb
  apply Segmentation.Tables.Range.chainOK_mergeWith <;> assumption
