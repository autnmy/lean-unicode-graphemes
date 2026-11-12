import Segmentation

-- "`Segmentation.boundaries : String → List Nat`, the cut positions counted in code points."
-- Mirrors GraphemeBreakTest.txt line 836, `0061 ÷ 1F1E6 × 1F1E7 × 200D ÷ 1F1E8 ÷ 0062`, with a stub
-- lookup: 'R' is RI, 'Z' is ZWJ, anything else is Other. The ZWJ joins the pair (GB9) and resets
-- the RI run, so the third RI is cut off. Expected cut positions: 0, 1, 4, 5, 6.
set_option maxRecDepth 20000 in
theorem «cutsOf breaks after an RI pair even when a ZWJ follows the pair (GB12/GB13, GraphemeBreakTest line 836)» :
    Segmentation.cutsOf
      (fun c =>
        if c = 'R' then { gcb := .RI, extPict := false, incb := .None }
        else if c = 'Z' then { gcb := .ZWJ, extPict := false, incb := .Extend }
        else { gcb := .Other, extPict := false, incb := .None })
      ['x', 'R', 'R', 'Z', 'R', 'x'] =
    [0, 1, 4, 5, 6] := by
  decide
