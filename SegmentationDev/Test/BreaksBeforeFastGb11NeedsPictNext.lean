import Segmentation

-- "Add `Segmentation.breaksBeforeFast (s : ScanState) (next : Props) : Bool` as a `match` on `s.prev` and `next.gcb`, with the GB9c (`s.linkerTail`, `incbIs .consonant`), GB11 (`s.zwjAfterPict`, `isExtPict`) and GB12/GB13 (`s.riOdd`) flag tests."
-- GB11 joins only when the next code point is Extended_Pictographic. A fallback arm that read
-- `s.zwjAfterPict` alone would join any code point after a pictograph's ZWJ and return false.
/-- After ZWJ following a pictograph, the fast decision breaks before a non-pictographic Other. -/
theorem breaks_before_fast_gb11_needs_pictographic_next :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .extend },
        linkerTail := false, pictTail := false, zwjAfterPict := true, riOdd := false }
      { gcb := .other, extPict := false, incb := .none } = true := by
  decide
