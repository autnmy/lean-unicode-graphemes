import Segmentation

-- "ZWJ after a pictograph, then a pictograph: no break."
/-- With the ZWJ-after-pictograph flag set, a following pictograph joins the cluster (GB11). -/
theorem breaksBeforeFast_zwj_after_pictograph_then_pictograph_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .extend },
        linkerTail := false, pictTail := false, zwjAfterPict := true, riOdd := false }
      { gcb := .other, extPict := true, incb := .none } = false := by
  decide
