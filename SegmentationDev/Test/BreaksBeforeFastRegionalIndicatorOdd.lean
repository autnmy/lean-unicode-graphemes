import Segmentation

-- "An odd regional-indicator run, then a regional indicator: no break."
/-- After an odd run of regional indicators, the next regional indicator joins it (GB12, GB13). -/
theorem breaksBeforeFast_odd_regional_indicator_run_then_regional_indicator_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := true }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = false := by
  decide
