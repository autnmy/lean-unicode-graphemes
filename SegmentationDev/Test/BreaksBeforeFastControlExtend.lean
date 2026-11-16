import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- After a Control code point, an Extend still breaks: GB4 comes before GB9. -/
theorem breaksBeforeFast_control_then_extend_breaks :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .extend, extPict := false, incb := .extend } = true := by
  decide
