import Segmentation

open Segmentation.Tables in
-- "Compute the combined table in Lean by merging the three sorted range lists into one sorted
-- list of ranges, each carrying a whole `Props`."
-- The inputs overlap (3..8 against 5..12), touch (13 right after 12) and leave gaps (0..2,
-- 15..19, above 22), so a wrong split point shows up as an unsorted result or a wrong value.
theorem «mergeWith_of_sorted_overlapping_lists_is_sorted_and_reads_both_values» :
    (let a : List (Range Nat) := [{ lo := 3, hi := 8, value := 1 }, { lo := 20, hi := 22, value := 2 }]
     let b : List (Range Bool) := [{ lo := 5, hi := 12, value := true }, { lo := 13, hi := 14, value := true }]
     let merged := Range.mergeWith Prod.mk 0 false a b
     Range.chainOK merged &&
       ([0, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 19, 20, 22, 23].map
          (fun n => Range.scanList (0, false) merged n)) ==
         [(0, false), (0, false), (1, false), (1, false), (1, true), (1, true), (0, true),
          (0, true), (0, true), (0, true), (0, false), (0, false), (2, false), (2, false),
          (0, false)]) = true := by
  decide
