import Segmentation

-- Mirrors GraphemeBreakTest.txt line 848, `0061 × 200D ÷ 1F6D1`, with a stub lookup: 'P' is
-- Extended_Pictographic, 'Z' is ZWJ, anything else is Other. A pictograph earlier in the text,
-- cut off by an ordinary letter, must not leave GB11 armed for the ZWJ after that letter.
set_option maxRecDepth 20000 in
theorem clustersOf_no_gb11_when_zwj_follows_non_pictograph_line_848 :
    Segmentation.clustersOf
      (fun c =>
        if c = 'P' then { gcb := .other, extPict := true, incb := .none }
        else if c = 'Z' then { gcb := .zwj, extPict := false, incb := .extend }
        else { gcb := .other, extPict := false, incb := .none })
      ['P', 'a', 'Z', 'P'] =
    [['P'], ['a', 'Z'], ['P']] := by
  decide
