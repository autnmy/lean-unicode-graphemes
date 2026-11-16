import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is the default."
-- GB4 (break after Control) comes before GB9 (no break before Extend). A match that put the
-- Extend arm ahead of the Control arm would join the Extend to the Control and return false.
/-- After a Control code point, the fast decision breaks before an Extend code point. -/
theorem breaks_before_fast_gb4_after_control_wins_over_gb9_extend :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .extend, extPict := false, incb := .extend } = true := by
  decide
