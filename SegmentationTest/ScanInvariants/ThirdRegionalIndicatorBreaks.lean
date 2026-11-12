import Segmentation

-- GB12 and GB13 join only an odd run of RI to the next RI. Before the third RI of RI, RI, RI
-- the run has even length, so neither applies and GB999 breaks at position 2.
theorem «a third regional indicator after an even pair starts a new cluster» :
    Segmentation.IsBoundary
      (fun _ => ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props))
      ['r', 'r', 'r'] 2 :=
  (Segmentation.breaksBefore_iff_isBoundary
      (fun _ => ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props))
      'r' ['r', 'r'] 1 (by decide)).mp (by decide)
