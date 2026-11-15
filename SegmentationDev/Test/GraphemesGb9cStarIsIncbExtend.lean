import Segmentation

-- GB9c's left side in Segmentation.rules is InCB Linker then InCB Extend*. Stub lookup: 'L' is
-- a linker (GCB Extend, InCB Linker), 'e' is GCB Extend but InCB None, 'K' is InCB Consonant.
-- 'e' joins by GB9, but it ends the linker run, so GB9c does not hold before 'K' and GB999
-- breaks. A state that counted GCB Extend as part of the run would join 'K'.
set_option maxRecDepth 20000 in
theorem clustersOf_no_gb9c_across_gcb_extend_without_incb_extend :
    Segmentation.clustersOf
      (fun c =>
        if c = 'L' then { gcb := .extend, extPict := false, incb := .linker }
        else if c = 'e' then { gcb := .extend, extPict := false, incb := .none }
        else if c = 'K' then { gcb := .other, extPict := false, incb := .consonant }
        else { gcb := .other, extPict := false, incb := .none })
      ['L', 'e', 'K'] =
    [['L', 'e'], ['K']] := by
  decide
