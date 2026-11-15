import Segmentation

-- Stub lookup: 'L' is a linker (GCB Extend, InCB Linker), 'x' is Other with InCB None, 'K' is
-- InCB Consonant. The text before 'K' ends with 'x', not with a linker run, so GB9c does not
-- hold and GB999 breaks. A linker flag that survived the cluster break at 'x' would join 'x K'.
set_option maxRecDepth 20000 in
theorem clustersOf_clears_gb9c_state_at_other_code_point_line_858 :
    Segmentation.clustersOf
      (fun c =>
        if c = 'L' then { gcb := .extend, extPict := false, incb := .linker }
        else if c = 'K' then { gcb := .other, extPict := false, incb := .consonant }
        else { gcb := .other, extPict := false, incb := .none })
      ['K', 'L', 'x', 'K'] =
    [['K', 'L'], ['x'], ['K']] := by
  decide
