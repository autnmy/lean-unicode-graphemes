import Segmentation

-- "`Segmentation.breaksBeforeFast` exists, and `breaksBeforeFast_eq_breaksBefore` proves it equal to `breaksBefore` for every state and properties."
-- The GB12/GB13 row of `breakRows` tests `s.riOdd` and the next class only, never `s.prev`.
-- So for a state whose `riOdd` is set while `prev` is Other, the reference says no break. A fast
-- arm that also required the previous class to be a regional indicator would break here, and
-- would hold only on reachable states, not on every state.
/-- With the odd-run flag set, the fast decision joins a regional indicator whatever the previous class. -/
theorem breaks_before_fast_gb12_reads_ri_flag_not_previous_class :
    Segmentation.breaksBeforeFast
      { prev := { gcb := .other, extPict := false, incb := .none },
        linkerTail := false, pictTail := false, zwjAfterPict := false, riOdd := true }
      { gcb := .regionalIndicator, extPict := false, incb := .none } = false := by
  decide
