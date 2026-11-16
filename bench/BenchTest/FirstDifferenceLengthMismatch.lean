import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- A comparison that zips the lists would miss a list that is only longer.
theorem «firstDifference reports a length mismatch at the index where the shorter list ends» :
    ((Bench.firstDifference "ascii" ["a", "b"] ["a", "b", "c"] ["a", "b", "c"]).map
        (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))
      == some ("ascii", 2, none, some "c", some "c")) = true := by
  decide
