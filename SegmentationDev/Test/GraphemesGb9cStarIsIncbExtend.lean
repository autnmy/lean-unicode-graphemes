import Segmentation

-- GB9c's left side in Segmentation.rules is InCB Linker then InCB Extend*. Stub lookup: 'L' is
-- a linker (GCB Extend, InCB Linker), 'e' is GCB Extend but InCB None, 'K' is InCB Consonant.
-- 'e' joins by GB9, but it ends the linker run, so GB9c does not hold before 'K' and GB999
-- breaks. A state that counted GCB Extend as part of the run would join 'K'.
set_option maxRecDepth 20000 in
theorem «clustersOf does not apply GB9c across a GCB Extend mark that is not InCB Extend» :
    Segmentation.clustersOf
      (fun c =>
        if c = 'L' then { gcb := .Extend, extPict := false, incb := .Linker }
        else if c = 'e' then { gcb := .Extend, extPict := false, incb := .None }
        else if c = 'K' then { gcb := .Other, extPict := false, incb := .Consonant }
        else { gcb := .Other, extPict := false, incb := .None })
      ['L', 'e', 'K'] =
    [['L', 'e'], ['K']] := by
  decide
