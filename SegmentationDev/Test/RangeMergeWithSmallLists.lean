import Segmentation

-- The first list has a gap at 5..7; the second overlaps both of its ranges, shares the end 12
-- with the first list, and has two ranges that touch at 12 and 13. Every point from 0 to 19 must
-- scan in the merged list as the pair of the two lists' own scans, and the merged list must stay
-- sorted with no empty or overlapping range.
open Segmentation.Tables in
theorem «mergeWith scans as the pair of scans across overlaps, gaps and touching ranges» :
    (let a : List (Range Nat) :=
        [{ lo := 0, hi := 4, value := 1 }, { lo := 8, hi := 12, value := 2 }]
     let b : List (Range Nat) :=
        [{ lo := 3, hi := 9, value := 5 }, { lo := 12, hi := 12, value := 6 },
         { lo := 13, hi := 15, value := 7 }]
     let merged := Range.mergeWith Prod.mk 0 0 a b
     Range.chainOK merged &&
       (List.range 20).all (fun n =>
         Range.scanList (0, 0) merged n == (Range.scanList 0 a n, Range.scanList 0 b n))) = true := by
  decide
