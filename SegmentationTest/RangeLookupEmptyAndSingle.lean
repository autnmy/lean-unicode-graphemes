import Segmentation.Tables.Range

theorem «range lookup on an empty table returns the default and a single range hits at lo and hi» :
    (Segmentation.Tables.Range.lookup (7 : Nat) (#[] : Array (Segmentation.Tables.Range Nat)) 0,
     [0x2FF, 0x300, 0x36F, 0x370].map fun n =>
      Segmentation.Tables.Range.lookup (0 : Nat)
        #[({ lo := 0x300, hi := 0x36F, value := 5 } : Segmentation.Tables.Range Nat)] n)
      = (7, [0, 5, 5, 0]) := by
  decide
