import Segmentation

-- "Do not land an unproved fast path behind a later proof, and do not weaken a statement to make a proof go through."
-- The equality must apply to any state and any properties, with no side condition such as a
-- reachable-state hypothesis; if it took one, this application would not type-check.
/-- The equality theorem applies to an arbitrary scan state and properties with nothing else supplied. -/
theorem breaks_before_fast_eq_holds_with_no_hypothesis
    (s : Segmentation.ScanState) (next : Segmentation.Props) :
    Segmentation.breaksBeforeFast s next = Segmentation.breaksBefore s next :=
  Segmentation.breaksBeforeFast_eq_breaksBefore s next
