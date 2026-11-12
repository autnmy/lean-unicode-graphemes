import Segmentation

open Segmentation in
-- Every code point reads as RI, so GB12/GB13 pair them from the start: cuts after each pair
-- and at the end, counted in code points.
theorem «cutsOf cuts a run of five regional indicators from a stub lookup after each pair» :
    (Segmentation.cutsOf (fun _ => { gcb := GCB.RI, extPict := false, incb := InCB.None })
      ['x', 'x', 'x', 'x', 'x'] == [0, 2, 4, 5]) = true := by
  decide

open Segmentation in
-- With no rule but GB999 applying, every code point is a cluster of its own.
theorem «clustersOf gives one cluster per code point when every code point is Other» :
    (Segmentation.clustersOf (fun _ => { gcb := GCB.Other, extPict := false, incb := InCB.None })
      ['a', 'b', 'c'] == [['a'], ['b'], ['c']]) = true := by
  decide
