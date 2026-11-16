import Bench.Compare

-- "A trailing empty cluster on the fast list only is reported."
/-- An extra empty cluster at the end of the fast list only is a difference, not agreement. -/
theorem firstDifference_reports_fast_trailing_empty_cluster :
    ((Bench.firstDifference "ascii" ["a"] ["a"] ["a", ""]).map
      (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))) =
    some ("ascii", 1, none, none, some "") := by
  decide
