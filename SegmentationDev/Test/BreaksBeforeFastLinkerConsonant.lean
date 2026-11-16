import Segmentation

-- "with the GB9c (`s.linkerTail`, `incbIs .consonant`), GB11 (`s.zwjAfterPict`, `isExtPict`) and
-- GB12/GB13 (`s.riOdd`) flag tests."
/-- With the linker flag set, a following InCB consonant joins the cluster (GB9c). -/
theorem breaksBeforeFast_linker_tail_then_consonant_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .extend, extPict := false, incb := .linker },
        linkerTail := true, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = false := by
  decide
