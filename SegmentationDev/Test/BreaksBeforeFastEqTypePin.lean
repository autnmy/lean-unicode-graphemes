import Segmentation

-- "Prove `breaksBeforeFast_eq_breaksBefore : ∀ s next, breaksBeforeFast s next = breaksBefore s next`."
/-- The equality theorem holds for every scan state and every next code point, with no hypothesis. -/
theorem breaksBeforeFast_eq_breaksBefore_holds_for_every_state :
    ∀ (s : Segmentation.ScanState) (next : Segmentation.Props),
      Segmentation.breaksBeforeFast s next = Segmentation.breaksBefore s next :=
  Segmentation.breaksBeforeFast_eq_breaksBefore
