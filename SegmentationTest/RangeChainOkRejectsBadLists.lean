import Segmentation

-- Each bad list is paired with valid ones, so a check that always answers false fails too.
open Segmentation.Tables in
theorem «Range.chainOK rejects out-of-order, overlapping, touching and reversed ranges and accepts a gapped list» :
    (Range.chainOK ([{ lo := 10, hi := 20, value := 1 }, { lo := 0, hi := 5, value := 2 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 10, value := 1 }, { lo := 10, hi := 20, value := 2 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 10, value := 1 }, { lo := 5, hi := 20, value := 2 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 5, hi := 3, value := 1 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 3, value := 1 }, { lo := 5, hi := 5, value := 2 },
                     { lo := 9, hi := 12, value := 1 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 3, value := 1 }, { lo := 4, hi := 6, value := 2 }] : List (Range Nat)),
     Range.chainOK ([] : List (Range Nat)))
      = (false, false, false, false, true, true, true) := by
  decide
