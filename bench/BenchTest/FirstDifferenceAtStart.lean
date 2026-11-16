import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
theorem «firstDifference reports index 0 when the first clusters differ» :
    ((Bench.firstDifference "emoji" ["a", "b"] ["z", "b"] ["z", "b"]).map
        (fun d => (d.index, d.ours, d.theirs, d.fast))
      == some (0, some "a", some "z", some "z")) = true := by
  decide
