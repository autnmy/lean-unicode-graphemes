import Segmentation

-- "L then V: no break."
/-- A Hangul L followed by a Hangul V stays in one cluster (GB6). -/
theorem breaksBeforeFast_l_then_v_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .l, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .v, extPict := false, incb := .none } = false := by
  decide
