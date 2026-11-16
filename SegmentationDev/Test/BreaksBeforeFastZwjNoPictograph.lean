import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- A ZWJ not preceded by a pictograph leaves the flag clear, so a following pictograph breaks. -/
theorem breaksBeforeFast_zwj_without_pictograph_then_pictograph_breaks :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .extend },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := true, incb := .none } = true := by
  decide
