import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- The lists differ at index 1 and again at index 3; only the first one may be reported.
theorem «firstDifference reports the earliest of two differing clusters» :
    (Bench.firstDifference "ascii" ["a", "b", "c", "d"] ["a", "B", "c", "D"]).map
        (fun d => (d.index, d.ours, d.theirs))
      = some (1, some "b", some "B") := by
  decide
