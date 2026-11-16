import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
/-- For every ASCII code point, the ASCII decision equals the full fast decision after states
whose flags are all set, after a Prepend, after a CR and after an odd regional indicator, so the
first ASCII code point after non-ASCII text is decided exactly. -/
theorem ascii_breaks_before_matches_fast_decision_after_armed_states :
    ∀ n < 128,
      Segmentation.breaksBeforeFast
          { prev := { gcb := .zwj, extPict := false, incb := .linker },
            linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
          (Segmentation.asciiProps n) = Segmentation.asciiBreaksBefore .zwj n ∧
      Segmentation.breaksBeforeFast
          { prev := { gcb := .prepend, extPict := false, incb := .none },
            linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
          (Segmentation.asciiProps n) = Segmentation.asciiBreaksBefore .prepend n ∧
      Segmentation.breaksBeforeFast
          { prev := { gcb := .cr, extPict := false, incb := .none },
            linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
          (Segmentation.asciiProps n) = Segmentation.asciiBreaksBefore .cr n ∧
      Segmentation.breaksBeforeFast
          { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
            linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := true }
          (Segmentation.asciiProps n) = Segmentation.asciiBreaksBefore .regionalIndicator n := by
  decide
