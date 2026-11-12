import Segmentation

open Segmentation.Tables in
theorem «Range.scan gives the value at both ends of a range and the default in a gap, past the end and on an empty table» :
    let table : Array (Range Nat) :=
      #[{ lo := 10, hi := 20, value := 1 }, { lo := 30, hi := 30, value := 2 }]
    (Range.scan 0 table 10, Range.scan 0 table 20, Range.scan 0 table 21,
     Range.scan 0 table 9, Range.scan 0 table 30, Range.scan 0 table 31,
     Range.scan 7 (#[] : Array (Range Nat)) 5)
      = (1, 1, 0, 0, 2, 0, 7) := by
  decide
