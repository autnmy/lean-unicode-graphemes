import Lean
import SegmentationDev.Gate.Axioms
import Segmentation

/-!
# The slice scanner's match-based break decision

`Segmentation.breaksBeforeFast` decides a boundary with one `match` on the previous and next
Grapheme_Cluster_Break values, and `breaksBeforeFast_eq_breaksBefore` proves it equal to the
reference `breaksBefore` for every scan state. The checks below run the match itself on the
cases the rules name, never through the equality, so a wrong arm fails here even though the
equality would also catch it. This module holds the five named cases, their flag-clear
counterparts, the rule-order cases, the type of the equality, the check that the scanner calls
the match, and the axiom gate on the equality.
-/

-- "CR then LF: no break."
/-- A CR followed by an LF is not a boundary (GB3), decided by the fast match itself. -/
theorem breaksBeforeFast_cr_then_lf_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .cr, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .lf, extPict := false, incb := .none } = false := by
  decide

-- "Control then Other: a break."
/-- A Control code point followed by an Other code point is a boundary (GB4). -/
theorem breaksBeforeFast_control_then_other_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .none } = true := by
  decide

-- "L then V: no break."
/-- A Hangul L followed by a Hangul V is not a boundary (GB6). -/
theorem breaksBeforeFast_l_then_v_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .l, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .v, extPict := false, incb := .none } = false := by
  decide

-- "ZWJ after a pictograph, then a pictograph: no break."
/-- A ZWJ that follows a pictograph, then another pictograph, is not a boundary (GB11). -/
theorem breaksBeforeFast_zwj_after_pictograph_then_pictograph_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := true, riOdd := false }
      { gcb := .other, extPict := true, incb := .none } = false := by
  decide

/-- A ZWJ with no pictograph before it, then a pictograph, is a boundary: the GB11 join reads
the zwjAfterPict flag, so a fast match that ignored the flag fails here. -/
theorem breaksBeforeFast_zwj_without_pictograph_then_pictograph_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := true, incb := .none } = true := by
  decide

-- GB11 joins only when the next code point is Extended_Pictographic. A fallback arm that read
-- `s.zwjAfterPict` alone would join any code point after a pictograph's ZWJ and return false.
/-- After ZWJ following a pictograph, the fast decision breaks before a non-pictographic Other. -/
theorem breaksBeforeFast_gb11_needs_pictographic_next :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .extend },
        linkerTail := false, pictTail := false, zwjAfterPict := true, riOdd := false }
      { gcb := .other, extPict := false, incb := .none } = true := by
  decide

-- "An odd regional-indicator run, then a regional indicator: no break."
/-- After an odd run of regional indicators, the next regional indicator joins it (GB12 and
GB13). -/
theorem breaksBeforeFast_odd_regional_indicator_run_then_indicator_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := true }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = false := by
  decide

/-- After an even run of regional indicators, the next regional indicator starts a new
cluster: the GB12 and GB13 join reads the riOdd flag, so a match that ignored it fails here. -/
theorem breaksBeforeFast_even_regional_indicator_run_then_indicator_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = true := by
  decide

-- The GB12/GB13 row of `breakRows` tests `s.riOdd` and the next class only, never `s.prev`.
-- So for a state whose `riOdd` is set while `prev` is Other, the reference says no break. A fast
-- arm that also required the previous class to be a regional indicator would break here, and
-- would hold only on reachable states, not on every state.
/-- With the odd-run flag set, the fast decision joins a regional indicator whatever the previous class. -/
theorem breaksBeforeFast_gb12_reads_ri_flag_not_previous_class :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .other, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := true }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = false := by
  decide

/-- After an InCB Linker tail, a next code point with InCB Consonant joins the cluster (GB9c),
read from the linkerTail flag and the next code point's InCB value. -/
theorem breaksBeforeFast_linker_tail_then_consonant_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .extend, extPict := false, incb := .linker },
        linkerTail := true, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = false := by
  decide

/-- With no InCB Linker tail, a next code point with InCB Consonant starts a new cluster: the
GB9c join reads the linkerTail flag, so a match that ignored it fails here. -/
theorem breaksBeforeFast_no_linker_tail_then_consonant_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .other, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = true := by
  decide

/-- With the linker flag clear, an InCB consonant after an Extend breaks by default. -/
theorem breaksBeforeFast_no_linker_tail_then_consonant_breaks :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .extend, extPict := false, incb := .extend },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = true := by
  decide

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- A Control code point followed by an Extend code point is a boundary: GB4 comes before GB9,
so the break after a control wins over the extend join. -/
theorem breaksBeforeFast_control_then_extend_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .extend, extPict := false, incb := .none } = true := by
  decide

-- GB5 (break before Control) comes before GB9b (no break after Prepend). A match that tested the
-- Prepend arm first would join the Control to the Prepend and return false.
/-- After a Prepend code point, the fast decision still breaks before a Control code point. -/
theorem breaksBeforeFast_gb5_before_control_wins_over_gb9b_prepend :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .prepend, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .control, extPict := false, incb := .none } = true := by
  decide

/-- A Prepend code point followed by an LF is a boundary: GB5 comes before GB9b, so the break
before a line feed wins over the prepend join. -/
theorem breaksBeforeFast_prepend_then_lf_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .prepend, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .lf, extPict := false, incb := .none } = true := by
  decide

-- GB3 (CR LF, no break) is the first row, ahead of GB4 (break after CR). Set flags must not
-- change that. A match that tested "prev is CR" for a break before the CR LF pair returns true.
/-- CR then LF is not a boundary in the fast decision, whatever the look-back flags hold. -/
theorem breaksBeforeFast_gb3_cr_lf_joins_with_every_flag_set :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .cr, extPict := false, incb := .none },
        linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      { gcb := .lf, extPict := false, incb := .none } = false := by
  decide

-- GB4 comes before GB9c, GB11 and GB12/GB13 in `breakRows`. With every flag set and a next code
-- point that each flag rule would join (a pictographic regional indicator with InCB Consonant),
-- the break after Control or LF must still win. A match that tested the flags first returns false.
/-- With every join flag set and a next code point that each flag test would join, a Control
before it is still a boundary. -/
theorem breaksBeforeFast_flags_set_after_control_still_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      { gcb := .regionalIndicator, extPict := true, incb := .consonant } = true := by
  decide

/-- After LF, the fast decision breaks even when every look-back flag is set. -/
theorem breaksBeforeFast_set_flags_never_override_gb4_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .lf, extPict := false, incb := .none },
        linkerTail := true, pictTail := true, zwjAfterPict := true, riOdd := true }
      { gcb := .regionalIndicator, extPict := true, incb := .consonant } = true := by
  decide

-- "Prove `breaksBeforeFast_eq_breaksBefore : ∀ s next, breaksBeforeFast s next = breaksBefore s
-- next`." "Do not weaken a statement to make a proof go through."
-- If the equality took a side condition, such as a reachable-state hypothesis, this stated type
-- would not be accepted as the theorem's own.
/-- The equality theorem holds for every scan state and every set of properties, with no
hypothesis. -/
theorem breaksBeforeFast_equals_breaksBefore_for_every_state :
    ∀ (s : Segmentation.ScanState) (next : Segmentation.Props),
      Segmentation.breaksBeforeFast s next = Segmentation.breaksBefore s next :=
  Segmentation.breaksBeforeFast_eq_breaksBefore

-- "`scanClusters` uses `breaksBeforeFast`, and `sliceGraphemes_agree`,
-- `graphemes_eq_graphemesFast` and `boundaries_eq_boundariesFast` still prove."
-- The agreement proofs hold whichever decision the scanner calls, so only its definition can show
-- the switch. The walk follows definitions in `Segmentation`, so a call through the
-- well-founded recursion's auxiliary definitions is found too.
open Lean in
/-- The scanner's definition reaches the fast break decision and never the reference one. -/
theorem scanClusters_reaches_breaksBeforeFast_not_breaksBefore : True := by
  run_tac do
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Segmentation.scanClusters]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if n == ``Segmentation.breaksBefore then
        throwError m!"Segmentation.scanClusters reaches the reference Segmentation.breaksBefore"
      if seen.contains n then continue
      seen := seen.insert n
      if (`Segmentation).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do
            todo := todo.push c
        | _ => pure ()
    unless seen.contains ``Segmentation.breaksBeforeFast do
      throwError m!"Segmentation.scanClusters does not reach Segmentation.breaksBeforeFast"
  trivial

-- "cover the new theorem in the axiom gate in `SegmentationDev/Gate/Axioms.lean`. It may use no
-- axiom beyond the ones the existing four statements use."
#assert_axioms Segmentation.breaksBeforeFast_eq_breaksBefore
