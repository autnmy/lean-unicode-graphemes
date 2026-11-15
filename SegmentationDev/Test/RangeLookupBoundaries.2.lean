import Segmentation.Tables.Range

theorem «range lookup hits both ends of each range and returns the default in gaps and past the end» :
    ([0x41, 0x5A, 0x5B, 0x60, 0x61, 0x7A, 0x7B, 0x40, 0, 0x10FFFF].map fun n =>
      Segmentation.Tables.Range.lookup (0 : Nat)
        #[({ lo := 0x41, hi := 0x5A, value := 1 } : Segmentation.Tables.Range Nat),
          { lo := 0x61, hi := 0x7A, value := 2 }] n)
      = [1, 1, 0, 0, 2, 2, 0, 0, 0, 0] := by
  decide
