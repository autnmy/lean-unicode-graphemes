import Segmentation

open Segmentation in
-- Every code point reads as RI, so GB12/GB13 pair them from the start and the fifth stands alone.
theorem «clustersOf pairs a run of five regional indicators from a stub lookup» :
    (Segmentation.clustersOf (fun _ => { gcb := GCB.RI, extPict := false, incb := InCB.None })
      ['x', 'x', 'x', 'x', 'x'] == [['x', 'x'], ['x', 'x'], ['x']]) = true := by
  decide
