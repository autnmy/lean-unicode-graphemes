import Segmentation

open Segmentation.Tables in
-- Each consecutive pair has `hi < next.lo` (2 < 10 and 4 < 6), but the middle range has
-- `lo > hi`, so the first and last ranges are not ordered by that chain. Only the per-range
-- `lo ≤ hi` check catches it.
theorem «chainOK rejects an inverted range even when every neighbour pair is ordered» :
    Range.chainOK ([⟨1, 2, 0⟩, ⟨10, 4, 0⟩, ⟨6, 7, 0⟩] : List (Range Nat)) = false := by
  decide
