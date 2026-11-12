import Segmentation

-- Stub lookup: 'L' is a linker (GCB Extend, InCB Linker), 'x' is Other with InCB None, 'K' is
-- InCB Consonant. The text before 'K' ends with 'x', not with a linker run, so GB9c does not
-- hold and GB999 breaks. A linker flag that survived the cluster break at 'x' would join 'x K'.
set_option maxRecDepth 20000 in
theorem «clustersOf clears the GB9c state at a code point that is neither linker nor InCB Extend (GraphemeBreakTest line 858 order)» :
    Segmentation.clustersOf
      (fun c =>
        if c = 'L' then { gcb := .Extend, extPict := false, incb := .Linker }
        else if c = 'K' then { gcb := .Other, extPict := false, incb := .Consonant }
        else { gcb := .Other, extPict := false, incb := .None })
      ['K', 'L', 'x', 'K'] =
    [['K', 'L'], ['x'], ['K']] := by
  decide
