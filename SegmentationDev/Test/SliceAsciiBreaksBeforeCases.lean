import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- The ASCII decision reads only the previous Grapheme_Cluster_Break value and the next byte:
-- CR then LF joins (GB3); CR, LF or a control after anything breaks (GB4, GB5); a printable byte
-- after a Prepend joins (GB9b), but a control byte after a Prepend breaks (GB5 comes first);
-- every other printable byte breaks (GB999).
/-- The ASCII break decision gives the rule verdicts for CR LF, CR CR, LF CR, Prepend then a
letter, Prepend then CR, Control then a letter, and a letter after a letter. -/
theorem ascii_breaks_before_decides_gb3_gb4_gb5_gb9b_and_default :
    (Segmentation.asciiBreaksBefore .cr 0x0A == false &&
      Segmentation.asciiBreaksBefore .cr 0x0D &&
      Segmentation.asciiBreaksBefore .lf 0x0D &&
      Segmentation.asciiBreaksBefore .prepend 0x61 == false &&
      Segmentation.asciiBreaksBefore .prepend 0x0D &&
      Segmentation.asciiBreaksBefore .control 0x61 &&
      Segmentation.asciiBreaksBefore .other 0x61 &&
      Segmentation.asciiBreaksBefore .extend 0x7F) = true := by
  decide
