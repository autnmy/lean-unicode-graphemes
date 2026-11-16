import Lean
import SegmentationDev.Gate.Axioms
import Segmentation

/-!
# The slice scanner's match-based break decision

`Segmentation.breaksBeforeFast` decides a boundary with one `match` on the previous and next
Grapheme_Cluster_Break values, and `breaksBeforeFast_eq_breaksBefore` proves it equal to the
reference `breaksBefore` for every scan state. The checks below run the match itself on the
cases the rules name, never through the equality, so a wrong arm fails here even though the
equality would also catch it. The other `BreaksBeforeFast*` modules hold the rule-order and
flag cases; this one holds the five named cases, the flag-clear counterparts, the check that
the scanner calls the match, and the axiom gate on the equality.
-/

-- "CR then LF: no break."
/-- A CR followed by an LF is not a boundary (GB3), decided by the fast match itself. -/
theorem breaks_before_fast_cr_then_lf_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .cr, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .lf, extPict := false, incb := .none } = false := by
  decide

-- "Control then Other: a break."
/-- A Control code point followed by an Other code point is a boundary (GB4). -/
theorem breaks_before_fast_control_then_other_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .none } = true := by
  decide

-- "L then V: no break."
/-- A Hangul L followed by a Hangul V is not a boundary (GB6). -/
theorem breaks_before_fast_l_then_v_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .l, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .v, extPict := false, incb := .none } = false := by
  decide

-- "ZWJ after a pictograph, then a pictograph: no break."
/-- A ZWJ that follows a pictograph, then another pictograph, is not a boundary (GB11). -/
theorem breaks_before_fast_zwj_after_pictograph_then_pictograph_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := true, riOdd := false }
      { gcb := .other, extPict := true, incb := .none } = false := by
  decide

/-- A ZWJ with no pictograph before it, then a pictograph, is a boundary: the GB11 join reads
the zwjAfterPict flag, so a fast match that ignored the flag fails here. -/
theorem breaks_before_fast_zwj_without_pictograph_then_pictograph_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .zwj, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := true, incb := .none } = true := by
  decide

-- "An odd regional-indicator run, then a regional indicator: no break."
/-- After an odd run of regional indicators, the next regional indicator joins it (GB12 and
GB13). -/
theorem breaks_before_fast_odd_regional_indicator_run_then_indicator_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .regionalIndicator, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := true }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = false := by
  decide

-- "Keep the same rule order as `breakRows`: the first row that applies decides, and a break is
-- the default."
/-- A Control code point followed by an Extend code point is a boundary: GB4 comes before GB9,
so the break after a control wins over the extend join. -/
theorem breaks_before_fast_control_then_extend_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .control, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .extend, extPict := false, incb := .none } = true := by
  decide

/-- After an InCB Linker tail, a next code point with InCB Consonant joins the cluster (GB9c),
read from the linkerTail flag and the next code point's InCB value. -/
theorem breaks_before_fast_linker_tail_then_consonant_is_no_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .extend, extPict := false, incb := .linker },
        linkerTail := true, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = false := by
  decide

/-- With no InCB Linker tail, a next code point with InCB Consonant starts a new cluster: the
GB9c join reads the linkerTail flag, so a match that ignored it fails here. -/
theorem breaks_before_fast_no_linker_tail_then_consonant_is_a_break :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .other, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := false }
      { gcb := .other, extPict := false, incb := .consonant } = true := by
  decide

-- "`scanClusters` uses `breaksBeforeFast`, and `sliceGraphemes_agree`,
-- `graphemes_eq_graphemesFast` and `boundaries_eq_boundariesFast` still prove."
-- The agreement proofs hold whichever decision the scanner calls, so only its definition can show
-- the switch. The walk follows definitions in `Segmentation`, so a call through the
-- well-founded recursion's auxiliary definitions is found too.
open Lean in
/-- The scanner's definition reaches the fast break decision and never the reference one. -/
theorem scan_clusters_reaches_breaks_before_fast_not_breaks_before : True := by
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
