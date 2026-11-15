import Segmentation

-- "Compute the combined table in Lean by merging the three sorted range lists into one sorted
-- list of ranges, each carrying a whole `Props`."
-- The binary search is only right on a sorted table, so a merge that emits an empty range
-- (lo > hi) or two overlapping pieces at a shared endpoint must fail here.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «mergeWith output of overlapping and touching ranges is still sorted» :
    (Range.chainOK
      (Range.mergeWith (fun (x : Nat) (y : Bool) => (x, y)) 0 false
        [({ lo := 0, hi := 10, value := 1 } : Range Nat), { lo := 20, hi := 30, value := 2 }]
        [({ lo := 5, hi := 20, value := true } : Range Bool), { lo := 31, hi := 40, value := true }])) =
      true := by
  decide
