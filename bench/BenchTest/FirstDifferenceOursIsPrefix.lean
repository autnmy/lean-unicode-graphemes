import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- A comparison that zips the two lists stops at the shorter one and would report no difference here.
theorem «firstDifference reports a missing final cluster when ours is a prefix of theirs» :
    (Bench.firstDifference "mixed" ["a", "b"] ["a", "b", "c"] ["a", "b", "c"]).map
        (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))
      = some ("mixed", 2, none, some "c", some "c") := by
  decide
