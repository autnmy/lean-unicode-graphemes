import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- A Prepend code point followed by an LF is a boundary: GB5 comes before GB9b, so the break
before a line feed wins over the prepend join. -/
theorem breaks_before_fast_prepend_then_lf_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .prepend, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .lf, extPict := false, incb := .none } = true := by
  decide
