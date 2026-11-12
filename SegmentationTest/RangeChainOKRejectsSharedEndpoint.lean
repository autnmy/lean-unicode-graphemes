import Segmentation

open Segmentation.Tables in
-- Code point 5 lies in both ranges, so the list overlaps. A check that only ordered ranges by
-- `lo`, or compared `hi ≤ next.lo`, would accept it and let the search and the scan disagree.
theorem «chainOK rejects ranges that share one code point» :
    Range.chainOK ([⟨1, 5, 1⟩, ⟨5, 8, 2⟩] : List (Range Nat)) = false := by
  decide
