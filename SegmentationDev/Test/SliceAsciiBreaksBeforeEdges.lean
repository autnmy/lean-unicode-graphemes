import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- The ASCII decision must still keep CR LF together (GB3), break after CR or LF before anything
-- else (GB4), let a control byte win over a preceding Prepend (GB5 comes before GB9b), and join a
-- printable byte to a preceding Prepend (GB9b). A shortcut that cuts before every ASCII byte except
-- LF after CR gets the Prepend cases wrong.
/-- The ASCII break decision gives the reference verdict on CR LF, on CR or LF before another
byte, and on a Prepend before a printable byte and before a control byte. -/
theorem ascii_breaks_before_keeps_gb3_gb5_and_gb9b_at_run_edges :
    (Segmentation.asciiBreaksBefore .cr 0x0A == false &&
      Segmentation.asciiBreaksBefore .cr 0x0D == true &&
      Segmentation.asciiBreaksBefore .cr 0x61 == true &&
      Segmentation.asciiBreaksBefore .lf 0x0D == true &&
      Segmentation.asciiBreaksBefore .lf 0x0A == true &&
      Segmentation.asciiBreaksBefore .prepend 0x61 == false &&
      Segmentation.asciiBreaksBefore .prepend 0x0D == true &&
      Segmentation.asciiBreaksBefore .prepend 0x0A == true &&
      Segmentation.asciiBreaksBefore .prepend 0x7F == true &&
      Segmentation.asciiBreaksBefore .extend 0x61 == true &&
      Segmentation.asciiBreaksBefore .regionalIndicator 0x61 == true &&
      Segmentation.asciiBreaksBefore .other 0x61 == true) = true := by
  decide
