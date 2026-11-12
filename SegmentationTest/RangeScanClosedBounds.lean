import Segmentation

open Segmentation.Tables in
-- A range holds `lo` to `hi`, both included. A half-open reference would miss `hi`, and a
-- reference that ignored the default would not give 0 at 1 and 5.
theorem «scan treats hi as included and gives the default just past it and just before lo» :
    (Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 2 = 7 ∧
     Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 4 = 7 ∧
     Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 5 = 0 ∧
     Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 1 = 0 ∧
     Range.scan 9 (#[] : Array (Range Nat)) 3 = 9) := by
  decide
