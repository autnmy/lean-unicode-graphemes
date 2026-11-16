import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
/-- The state the ASCII path moves to after any ASCII code point has the same break class and
flags as pushing that code point onto a state with every flag set: all flags clear, so a ZWJ,
linker or regional indicator before the run cannot join across it. -/
theorem ascii_state_clears_every_flag_left_before_the_run :
    ∀ n < 128,
      let armed : Segmentation.ScanState :=
        { prev := { gcb := .zwj, extPict := true, incb := .linker },
          linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      let pushed := armed.push (Segmentation.asciiProps n)
      (Segmentation.asciiState n).prev.gcb = (Segmentation.asciiProps n).gcb ∧
      (Segmentation.asciiState n).prev.gcb = pushed.prev.gcb ∧
      (Segmentation.asciiState n).linkerTail = pushed.linkerTail ∧
      (Segmentation.asciiState n).pictTail = pushed.pictTail ∧
      (Segmentation.asciiState n).zwjAfterPict = pushed.zwjAfterPict ∧
      (Segmentation.asciiState n).riOdd = pushed.riOdd ∧
      (Segmentation.asciiState n).linkerTail = false ∧
      (Segmentation.asciiState n).zwjAfterPict = false ∧
      (Segmentation.asciiState n).riOdd = false := by
  decide
