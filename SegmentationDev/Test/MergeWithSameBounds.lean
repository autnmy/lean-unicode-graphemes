import Segmentation

-- "Compute the combined table in Lean by merging the three sorted range lists into one sorted
-- list of ranges, each carrying a whole `Props`."
-- When both lists hold the same range, the merge must emit it once with both values, and must
-- not leave an empty piece that hides the code points next to it.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «mergeWith handles two ranges with the same lo and hi» :
    ([2, 3, 7, 8].map
      (Range.scanList ((0 : Nat), false)
        (Range.mergeWith (fun (x : Nat) (y : Bool) => (x, y)) 0 false
          [({ lo := 3, hi := 7, value := 5 } : Range Nat)]
          [({ lo := 3, hi := 7, value := true } : Range Bool)]))) =
      [(0, false), (5, true), (5, true), (0, false)] := by
  decide
