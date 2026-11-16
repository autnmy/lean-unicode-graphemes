import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is the default."
-- GB4 comes before GB9c, GB11 and GB12/GB13 in `breakRows`. With every flag set and a next code
-- point that each flag rule would join (a pictographic regional indicator with InCB Consonant),
-- the break after LF must still win. A match that tested the flags before the LF arm returns false.
/-- After LF, the fast decision breaks even when every look-back flag is set. -/
theorem breaks_before_fast_set_flags_never_override_gb4_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .lf, extPict := false, incb := .none },
        linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      { gcb := .regionalIndicator, extPict := true, incb := .consonant } = true := by
  decide
