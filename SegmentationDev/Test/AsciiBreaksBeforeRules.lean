import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
/-- The ASCII decision keeps CR with a following LF (GB3), breaks around other controls (GB4,
GB5), joins a printable ASCII code point to a preceding Prepend (GB9b) but not a control, and
breaks between ordinary code points. -/
theorem ascii_breaks_before_follows_gb3_gb4_gb5_gb9b :
    Segmentation.asciiBreaksBefore .cr 0x0A = false ∧
    Segmentation.asciiBreaksBefore .cr 0x61 = true ∧
    Segmentation.asciiBreaksBefore .cr 0x0D = true ∧
    Segmentation.asciiBreaksBefore .lf 0x0D = true ∧
    Segmentation.asciiBreaksBefore .lf 0x0A = true ∧
    Segmentation.asciiBreaksBefore .control 0x61 = true ∧
    Segmentation.asciiBreaksBefore .other 0x0A = true ∧
    Segmentation.asciiBreaksBefore .prepend 0x61 = false ∧
    Segmentation.asciiBreaksBefore .prepend 0x0D = true ∧
    Segmentation.asciiBreaksBefore .prepend 0x7F = true ∧
    Segmentation.asciiBreaksBefore .other 0x61 = true ∧
    Segmentation.asciiBreaksBefore .extend 0x61 = true ∧
    Segmentation.asciiBreaksBefore .zwj 0x20 = true := by
  decide
