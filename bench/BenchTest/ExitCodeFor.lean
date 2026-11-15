import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
theorem «exitCodeFor fails the job only when a difference was found» :
    (Bench.exitCodeFor none == 0
      && Bench.exitCodeFor (Bench.firstDifference "ascii" ["a"] ["b"]) == 1) = true := by
  decide
