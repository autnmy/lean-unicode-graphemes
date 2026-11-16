import Bench.Compare

-- "A fast list that is a strict prefix of the others is reported."
/-- A fast list that ends one cluster early is reported at the index where it ends, with the fast field empty. -/
theorem firstDifference_reports_fast_strict_prefix :
    ((Bench.firstDifference "ascii" ["a", "b"] ["a", "b"] ["a"]).map
      (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))) =
    some ("ascii", 1, some "b", some "b", none) := by
  decide
