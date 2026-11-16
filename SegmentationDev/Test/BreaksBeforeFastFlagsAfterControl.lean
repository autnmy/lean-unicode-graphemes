import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- With every join flag set and a next code point that each flag test would join, a Control
before it is still a boundary: GB4 comes before GB9c, GB11 and GB12, so no flag join overrides
it. -/
theorem breaks_before_fast_flags_set_after_control_still_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      { gcb := .regionalIndicator, extPict := true, incb := .consonant } = true := by
  decide
