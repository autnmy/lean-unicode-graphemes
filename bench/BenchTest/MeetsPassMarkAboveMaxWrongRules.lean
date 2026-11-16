import Bench.Report

-- "`meetsPassMark` passes at equality with UnicodeExtra's max and fails one nanosecond above, by
-- a test in `bench/BenchTest/`."
-- The fast median is 501 against a max of 500. Median to median (501 ≤ 600) and swapped
-- arguments (600 ≤ 700) would both give true, so only the stated rule gives false.
/-- A fast median one nanosecond above UnicodeExtra's maximum fails the pass mark. -/
theorem meets_pass_mark_false_one_above_max_where_wrong_rules_say_true :
    Bench.meetsPassMark { median := 501, min := 100, max := 700, count := 31 }
      { median := 600, min := 200, max := 500, count := 31 } = false := by
  decide
