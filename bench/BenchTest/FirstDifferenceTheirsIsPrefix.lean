import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- The length check must hold in both directions, not only when our list is the shorter one.
theorem «firstDifference reports a missing final cluster when theirs is a prefix of ours» :
    (Bench.firstDifference "emoji" ["x", "y", "z"] ["x"] ["x", "y", "z"]).map
        (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))
      = some ("emoji", 1, some "y", none, some "y") := by
  decide
