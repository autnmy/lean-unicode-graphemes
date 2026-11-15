import Segmentation

-- Segmentation.rules is read in order and the first rule that applies wins. Stub lookup: 'C' is
-- Control, 'E' is Extend, 'p' is Prepend. GB4 breaks after Control before GB9 can join the
-- Extend (as in GraphemeBreakTest.txt line 28); GB5 breaks before Control before GB9b can join
-- it to the Prepend. No rule joins Extend to a following Prepend (GB9b joins only after a
-- Prepend), so GB999 breaks there. A segmenter that checked GB9/GB9b first would join 'C' to
-- 'E' and 'p' to the last 'C'.
set_option maxRecDepth 20000 in
theorem clustersOf_gb4_gb5_win_over_gb9_gb9b :
    Segmentation.clustersOf
      (fun c =>
        if c = 'C' then { gcb := .control, extPict := false, incb := .none }
        else if c = 'E' then { gcb := .extend, extPict := false, incb := .extend }
        else if c = 'p' then { gcb := .prepend, extPict := false, incb := .none }
        else { gcb := .other, extPict := false, incb := .none })
      ['C', 'E', 'p', 'C'] =
    [['C'], ['E'], ['p'], ['C']] := by
  decide
