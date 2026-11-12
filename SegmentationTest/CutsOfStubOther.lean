import Segmentation

open Segmentation in
-- With no rule but GB999 applying, every position between code points is a cut, ends included.
theorem «cutsOf gives one cut per code point when every code point is Other» :
    (Segmentation.cutsOf (fun _ => { gcb := GCB.Other, extPict := false, incb := InCB.None })
      ['a', 'b', 'c'] == [0, 1, 2, 3]) = true := by
  decide
