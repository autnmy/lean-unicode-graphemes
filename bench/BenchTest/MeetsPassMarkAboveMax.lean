import Bench.Report

-- "`meetsPassMark` passes at equality with UnicodeExtra's max and fails one nanosecond above"
-- The fast min is below every UnicodeExtra figure, so a rule that read the fast min would pass.
/-- The pass mark is missed when the fast median is one nanosecond above UnicodeExtra's maximum sample. -/
theorem meetsPassMark_false_one_ns_above_theirs_max :
    Bench.meetsPassMark { median := 501, min := 100, max := 600, count := 3 }
      { median := 300, min := 200, max := 500, count := 3 } = false := by
  decide
