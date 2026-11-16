import Segmentation

/-!
# The ASCII break decision

"an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
following non-ASCII code point can join it"

`asciiBreaksBefore` reads only the previous Grapheme_Cluster_Break value and the next byte. The
checks below pin its verdict on each rule it stands for, and that it equals the full fast
decision for every incoming state, so the first ASCII code point after non-ASCII text is decided
exactly.
-/

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
    Segmentation.asciiBreaksBefore .zwj 0x20 = true ∧
    Segmentation.asciiBreaksBefore .extend 0x7F = true ∧
    Segmentation.asciiBreaksBefore .prepend 0x0A = true ∧
    Segmentation.asciiBreaksBefore .regionalIndicator 0x61 = true := by
  decide

/-- For every ASCII code point, the ASCII decision equals the full fast decision after states
whose flags are all set, after a Prepend, after a CR and after an odd regional indicator. -/
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

/-- For every scan state and every number, the full match on ASCII properties gives the same
verdict as the ASCII decision on the previous break class alone. -/
theorem breaks_before_fast_on_ascii_props_is_ascii_breaks_before_for_every_state :
    ∀ (s : Segmentation.ScanState) (n : Nat),
      Segmentation.breaksBeforeFast s (Segmentation.asciiProps n) =
        Segmentation.asciiBreaksBefore s.prev.gcb n :=
  Segmentation.breaksBeforeFast_asciiProps
