import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- After an even run of regional indicators, the next regional indicator starts a new pair. -/
theorem breaksBeforeFast_even_regional_indicator_run_then_regional_indicator_breaks :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = true := by
  decide
