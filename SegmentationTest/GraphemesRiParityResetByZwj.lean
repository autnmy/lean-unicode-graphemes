import Segmentation

-- "`Segmentation.graphemes : String → List String`, one pass over the input with a small state
-- for GB9c, GB11 and GB12/GB13 (the rules that look further back than one code point)."
-- Mirrors GraphemeBreakTest.txt line 837, `0061 ÷ 1F1E6 × 200D ÷ 1F1E7 × 1F1E8 ÷ 0062`, with a stub
-- lookup: 'R' is RI, 'Z' is ZWJ, anything else is Other. The ZWJ ends the RI run, so the second
-- RI starts a new pair. A state that kept counting RIs across the ZWJ would join it to the first.
set_option maxRecDepth 20000 in
theorem «clustersOf resets regional indicator parity at a ZWJ inside a flag run (GB12/GB13, GraphemeBreakTest line 837)» :
    Segmentation.clustersOf
      (fun c =>
        if c = 'R' then { gcb := .RI, extPict := false, incb := .None }
        else if c = 'Z' then { gcb := .ZWJ, extPict := false, incb := .Extend }
        else { gcb := .Other, extPict := false, incb := .None })
      ['x', 'R', 'Z', 'R', 'R', 'x'] =
    [['x'], ['R', 'Z'], ['R', 'R'], ['x']] := by
  decide
