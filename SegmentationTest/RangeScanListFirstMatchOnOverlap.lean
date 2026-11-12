import Segmentation

open Segmentation.Tables in
-- The reference is a plain first-match scan: on an overlapping list it must give the earlier
-- range's value, not the later one and not whatever a halving search would land on.
theorem «scanList returns the first matching range when two ranges overlap» :
    (Range.scanList 0 ([⟨1, 5, 10⟩, ⟨3, 8, 20⟩] : List (Range Nat)) 4 = 10 ∧
     Range.scanList 0 ([⟨1, 5, 10⟩, ⟨3, 8, 20⟩] : List (Range Nat)) 7 = 20 ∧
     Range.scan 0 (#[⟨1, 5, 10⟩, ⟨3, 8, 20⟩] : Array (Range Nat)) 4 = 10) := by
  decide
