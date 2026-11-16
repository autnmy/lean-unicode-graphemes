import Bench.Compare

-- "It reports the first index where the three heads are not all present and equal."
-- A walk that stops when this library's and UnicodeExtra's lists end would treat an extra
-- fast cluster as agreement and let the check pass.
/-- A fast list with one cluster more than the two equal lists is reported at that index. -/
theorem first_difference_reports_extra_fast_cluster :
    Bench.firstDifference "x" ["a"] ["a"] ["a", "b"] =
      some { input := "x", index := 1, ours := none, theirs := none, fast := some "b" } := by
  decide
