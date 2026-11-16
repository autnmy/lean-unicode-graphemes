import Segmentation

-- "Prove `breaksBeforeFast_eq_breaksBefore : ∀ s next, breaksBeforeFast s next = breaksBefore s
-- next`."
/-- The equality theorem holds for every scan state and every set of properties, with no
hypothesis: the stated type here must be accepted as the theorem's own type. -/
theorem breaks_before_fast_equals_breaks_before_for_every_state :
    ∀ (s : Segmentation.ScanState) (next : Segmentation.Props),
      Segmentation.breaksBeforeFast s next = Segmentation.breaksBefore s next :=
  Segmentation.breaksBeforeFast_eq_breaksBefore
