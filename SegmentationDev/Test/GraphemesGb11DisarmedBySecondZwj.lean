import Segmentation

-- "`Segmentation.graphemes : String → List String`, one pass over the input with a small state
-- for GB9c, GB11 and GB12/GB13 (the rules that look further back than one code point)."
-- GB11 joins only after ExtPict, then Extend*, then exactly one ZWJ. Stub lookup: 'P' is
-- Extended_Pictographic, 'E' is Extend, 'Z' is ZWJ. Before the last 'P' the text ends with
-- ZWJ ZWJ, which GB11's left side does not match, so GB999 breaks there. A state that stays
-- armed after any ZWJ would join the second pictograph.
set_option maxRecDepth 20000 in
theorem clustersOf_no_gb11_after_second_zwj :
    Segmentation.clustersOf
      (fun c =>
        if c = 'P' then { gcb := .other, extPict := true, incb := .none }
        else if c = 'E' then { gcb := .extend, extPict := false, incb := .extend }
        else if c = 'Z' then { gcb := .zwj, extPict := false, incb := .extend }
        else { gcb := .other, extPict := false, incb := .none })
      ['P', 'E', 'Z', 'Z', 'P'] =
    [['P', 'E', 'Z', 'Z'], ['P']] := by
  decide
