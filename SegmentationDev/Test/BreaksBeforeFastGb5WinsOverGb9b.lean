import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is the default."
-- GB5 (break before Control) comes before GB9b (no break after Prepend). A match that tested the
-- Prepend arm first would join the Control to the Prepend and return false.
/-- After a Prepend code point, the fast decision still breaks before a Control code point. -/
theorem breaks_before_fast_gb5_before_control_wins_over_gb9b_prepend :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .prepend, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .control, extPict := false, incb := .none } = true := by
  decide
