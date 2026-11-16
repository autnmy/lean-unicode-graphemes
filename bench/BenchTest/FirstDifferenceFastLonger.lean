import Bench.Compare

-- "It reports the first index where the three heads are not all present and equal."
/-- A fast list with one more cluster than the other two is reported at that extra cluster. -/
theorem firstDifference_reports_extra_fast_cluster :
    ((Bench.firstDifference "ascii" ["a"] ["a"] ["a", "b"]).map
      (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))) =
    some ("ascii", 1, none, none, some "b") := by
  decide
