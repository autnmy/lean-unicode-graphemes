import Segmentation

-- On an unsorted, overlapping list the reference still has one answer: the first range in list
-- order that holds `n`. Code point 5 lies in both ranges; 12 lies only in the second.
open Segmentation.Tables in
theorem «Range.scanList returns the first matching range in list order when ranges overlap» :
    let ranges : List (Range Nat) :=
      [{ lo := 0, hi := 9, value := 1 }, { lo := 5, hi := 15, value := 2 }]
    (Range.scanList 0 ranges 5, Range.scanList 0 ranges 12, Range.scanList 0 ranges 16,
     Range.scanList 4 ([] : List (Range Nat)) 0)
      = (1, 2, 0, 4) := by
  decide
