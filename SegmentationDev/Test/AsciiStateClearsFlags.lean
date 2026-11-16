import Segmentation

/-!
# The scan state after an ASCII code point

"an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
following non-ASCII code point can join it"

The ASCII path skips `ScanState.push`, so the state it leaves must be the one `push` would leave:
the byte's own properties and every look-back flag (GB9c, GB11, GB12/GB13) clear. A state that
kept a flag from before the run would join the next non-ASCII code point wrongly.
-/

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

/-- Pushing ASCII properties onto any state gives the ASCII state, and the ASCII state for a letter
holds that letter's properties with every flag false. -/
theorem push_of_ascii_props_is_ascii_state_with_every_flag_clear :
    (∀ (s : Segmentation.ScanState) (n : Nat),
      s.push (Segmentation.asciiProps n) = Segmentation.asciiState n) ∧
    Segmentation.asciiState 0x61 =
      { prev := Segmentation.asciiProps 0x61, linkerTail := false, pictTail := false,
        zwjAfterPict := false, riOdd := false } :=
  ⟨Segmentation.ScanState.push_asciiProps, rfl⟩

/-- The state after an ASCII byte holds that byte's properties and no look-back flag. -/
theorem ascii_state_clears_every_lookback_flag :
    ((Segmentation.asciiState 0x0D).prev.gcb == .cr &&
      (Segmentation.asciiState 0x0A).prev.gcb == .lf &&
      (Segmentation.asciiState 0x61).prev.gcb == .other &&
      (Segmentation.asciiState 0x01).prev.gcb == .control &&
      !(Segmentation.asciiState 0x61).linkerTail &&
      !(Segmentation.asciiState 0x61).pictTail &&
      !(Segmentation.asciiState 0x61).zwjAfterPict &&
      !(Segmentation.asciiState 0x61).riOdd) = true := by
  decide
