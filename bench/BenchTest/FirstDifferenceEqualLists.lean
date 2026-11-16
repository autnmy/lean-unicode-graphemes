import Bench.Compare

theorem «firstDifference reports no difference for equal cluster lists» :
    ((Bench.firstDifference "ascii" ["a", "b", "c"] ["a", "b", "c"] ["a", "b", "c"]).isNone
      && (Bench.firstDifference "ascii" [] [] []).isNone) = true := by
  decide
