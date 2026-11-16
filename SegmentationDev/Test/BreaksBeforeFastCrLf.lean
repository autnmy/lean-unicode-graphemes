import Segmentation

-- "CR then LF: no break."
/-- After a CR, a following LF is not a boundary (GB3 comes before GB4). -/
theorem breaksBeforeFast_cr_then_lf_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .cr, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .lf, extPict := false, incb := .none } = false := by
  decide
