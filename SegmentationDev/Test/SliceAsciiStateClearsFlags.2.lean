import Segmentation

-- "Every ASCII code point still goes through `asciiProps`, the break decision and `ScanState.push`."
-- The ASCII path skips `ScanState.push`, so the state it leaves must be the one `push` would leave:
-- the byte's own properties and every look-back flag cleared. A state that kept a GB11, GB9c or
-- regional-indicator flag from before the run would join the next non-ASCII code point wrongly.
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
