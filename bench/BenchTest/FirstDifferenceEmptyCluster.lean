import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- A comparison that joins the clusters back into one string would see "" and [""] as equal.
theorem «firstDifference treats an empty cluster as a difference against no cluster» :
    (Bench.firstDifference "large" [] [""] [""]).map
        (fun d => (d.index, d.ours, d.theirs, d.fast))
      = some (0, none, some "", some "") := by
  decide
