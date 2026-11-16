import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is the default."
-- GB3 (CR LF, no break) is the first row, ahead of GB4 (break after CR). Set flags must not
-- change that. A match that tested "prev is CR" for a break before the CR LF pair returns true.
/-- CR then LF is not a boundary in the fast decision, whatever the look-back flags hold. -/
theorem breaks_before_fast_gb3_cr_lf_joins_with_every_flag_set :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .cr, extPict := false, incb := .none },
        linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      { gcb := .lf, extPict := false, incb := .none } = false := by
  decide
