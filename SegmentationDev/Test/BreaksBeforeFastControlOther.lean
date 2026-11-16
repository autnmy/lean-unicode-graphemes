import Segmentation

-- "Control then Other: a break."
/-- After a Control code point, an Other code point starts a new cluster (GB4). -/
theorem breaksBeforeFast_control_then_other_breaks :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .none } = true := by
  decide
