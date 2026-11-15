import Segmentation

-- "Compute the combined table in Lean by merging the three sorted range lists into one sorted
-- list of ranges, each carrying a whole `Props`."
-- The ranges overlap (5..10), share an endpoint (20 ends one range and starts the other),
-- touch across lists (30 then 31), and leave gaps (11..19 in the first list, past 40 in both).
-- Each point read is one side of a cut, where an off-by-one (hi against lo - 1) shows up.
open Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «mergeWith keeps both values on each side of every split point» :
    ([0, 4, 5, 10, 11, 19, 20, 21, 30, 31, 40, 41].map
      (Range.scanList ((0 : Nat), false)
        (Range.mergeWith (fun (x : Nat) (y : Bool) => (x, y)) 0 false
          [({ lo := 0, hi := 10, value := 1 } : Range Nat), { lo := 20, hi := 30, value := 2 }]
          [({ lo := 5, hi := 20, value := true } : Range Bool), { lo := 31, hi := 40, value := true }]))) =
      [(1, false), (1, false), (1, true), (1, true), (0, true), (0, true), (2, true), (2, false),
        (2, false), (0, true), (0, true), (0, false)] := by
  decide
