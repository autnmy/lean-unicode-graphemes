import Segmentation

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- With the linker flag clear, an InCB consonant after an Extend breaks by default. -/
theorem breaksBeforeFast_no_linker_tail_then_consonant_breaks :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .extend, extPict := false, incb := .extend },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = true := by
  decide
