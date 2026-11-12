import Segmentation

theorem «lookup returns the range value at both ends and the default in gaps» :
    (let table : Array (Segmentation.Tables.Range Nat) :=
        #[{ lo := 0x41, hi := 0x5A, value := 1 }, { lo := 0x61, hi := 0x7A, value := 2 }]
     Segmentation.Tables.Range.lookup 0 table 0x41 == 1 &&
     Segmentation.Tables.Range.lookup 0 table 0x5A == 1 &&
     Segmentation.Tables.Range.lookup 0 table 0x5B == 0 &&
     Segmentation.Tables.Range.lookup 0 table 0x60 == 0 &&
     Segmentation.Tables.Range.lookup 0 table 0x61 == 2 &&
     Segmentation.Tables.Range.lookup 0 table 0x7A == 2 &&
     Segmentation.Tables.Range.lookup 0 table 0x10FFFF == 0 &&
     Segmentation.Tables.Range.lookup 7 (#[] : Array (Segmentation.Tables.Range Nat)) 0 == 7) = true := by
  decide
