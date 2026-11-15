import Segmentation

-- Mirrors GraphemeBreakTest.txt line 659, `1CF5 × 0915`: U+1CF5 is InCB Linker but not GCB
-- Extend. Stub lookup: 'J' is InCB Linker with GCB Other, 'K' is InCB Consonant with GCB Other.
-- No rule but GB9c joins them, and GB9c reads InCB only, so a state armed by GCB would break.
set_option maxRecDepth 20000 in
theorem clustersOf_applies_gb9c_to_linker_with_non_extend_gcb_line_659 :
    Segmentation.clustersOf
      (fun c =>
        if c = 'J' then { gcb := .other, extPict := false, incb := .linker }
        else if c = 'K' then { gcb := .other, extPict := false, incb := .consonant }
        else { gcb := .other, extPict := false, incb := .none })
      ['J', 'K'] =
    [['J', 'K']] := by
  decide
