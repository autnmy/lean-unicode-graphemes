import Segmentation

-- "Do not land an unproved fast path behind a later proof, and do not weaken a statement to make a
-- proof go through."
-- The ASCII decision must equal the full decision for every incoming scan state, flags included,
-- so the first ASCII byte after a non-ASCII code point (for example a Prepend) is decided exactly.
/-- For every scan state and every number, the full match on ASCII properties gives the same
verdict as the ASCII decision on the previous break class alone. -/
theorem breaks_before_fast_on_ascii_props_is_ascii_breaks_before_for_every_state :
    ∀ (s : Segmentation.ScanState) (n : Nat),
      Segmentation.breaksBeforeFast s (Segmentation.asciiProps n) =
        Segmentation.asciiBreaksBefore s.prev.gcb n :=
  Segmentation.breaksBeforeFast_asciiProps
