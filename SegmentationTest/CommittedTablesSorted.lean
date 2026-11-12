import Segmentation

-- "Any lemmas about sorted, non-overlapping ranges the generated tables need, checked against
-- the tables themselves."
open Segmentation.Tables in
theorem «the three committed tables are proved sorted and non-overlapping» :
    Range.Sorted gcbRanges ∧ Range.Sorted extPictRanges ∧ Range.Sorted incbRanges :=
  ⟨gcbRanges_sorted, extPictRanges_sorted, incbRanges_sorted⟩
