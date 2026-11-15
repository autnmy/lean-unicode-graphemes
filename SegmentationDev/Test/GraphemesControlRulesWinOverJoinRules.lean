import Segmentation

-- Segmentation.rules is read in order and the first rule that applies wins. Stub lookup: 'C' is
-- Control, 'E' is Extend, 'p' is Prepend. GB4 breaks after Control before GB9 can join the
-- Extend (as in GraphemeBreakTest.txt line 28); GB5 breaks before Control before GB9b can join
-- it to the Prepend. No rule joins Extend to a following Prepend (GB9b joins only after a
-- Prepend), so GB999 breaks there. A segmenter that checked GB9/GB9b first would join 'C' to
-- 'E' and 'p' to the last 'C'.
set_option maxRecDepth 20000 in
theorem «clustersOf lets GB4 and GB5 win over GB9 and GB9b (first matching rule wins)» :
    Segmentation.clustersOf
      (fun c =>
        if c = 'C' then { gcb := .Control, extPict := false, incb := .None }
        else if c = 'E' then { gcb := .Extend, extPict := false, incb := .Extend }
        else if c = 'p' then { gcb := .Prepend, extPict := false, incb := .None }
        else { gcb := .Other, extPict := false, incb := .None })
      ['C', 'E', 'p', 'C'] =
    [['C'], ['E'], ['p'], ['C']] := by
  decide
