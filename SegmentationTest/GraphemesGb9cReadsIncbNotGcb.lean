import Segmentation

-- Mirrors GraphemeBreakTest.txt line 659, `1CF5 × 0915`: U+1CF5 is InCB Linker but not GCB
-- Extend. Stub lookup: 'J' is InCB Linker with GCB Other, 'K' is InCB Consonant with GCB Other.
-- No rule but GB9c joins them, and GB9c reads InCB only, so a state armed by GCB would break.
set_option maxRecDepth 20000 in
theorem «clustersOf applies GB9c to a linker whose GCB is not Extend (GraphemeBreakTest line 659)» :
    Segmentation.clustersOf
      (fun c =>
        if c = 'J' then { gcb := .Other, extPict := false, incb := .Linker }
        else if c = 'K' then { gcb := .Other, extPict := false, incb := .Consonant }
        else { gcb := .Other, extPict := false, incb := .None })
      ['J', 'K'] =
    [['J', 'K']] := by
  decide
