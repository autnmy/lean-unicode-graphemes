import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
theorem «firstDifference reports the first differing cluster, not a later one» :
    ((Bench.firstDifference "mixed" ["a", "b", "c", "d", "e", "f"] ["a", "b", "c", "x", "e", "y"]).map
        (fun d => (d.index, d.ours, d.theirs))
      == some (3, some "d", some "x")) = true := by
  decide
