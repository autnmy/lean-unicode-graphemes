import Segmentation

/-- After an even run of regional indicators, the next regional indicator starts a new
cluster: the GB12 and GB13 join reads the riOdd flag, so a match that ignored it fails here. -/
theorem breaks_before_fast_even_regional_indicator_run_then_indicator_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = true := by
  decide
