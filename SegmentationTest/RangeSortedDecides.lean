import Segmentation

open Segmentation.Tables in
theorem «Range.Sorted holds for a gapped array and fails for an array whose second range reaches back over the first» :
    Range.Sorted (#[{ lo := 0, hi := 3, value := 1 }, { lo := 7, hi := 9, value := 2 }] : Array (Range Nat)) ∧
      ¬ Range.Sorted (#[{ lo := 0, hi := 8, value := 1 }, { lo := 7, hi := 9, value := 2 }] : Array (Range Nat)) := by
  decide
