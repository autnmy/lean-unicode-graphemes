import Bench.Report

-- "Add a pure `Bench.meetsPassMark (fast theirs : Bench.Stats) : Bool` that is `fast.median ≤ theirs.max`."
-- The fast max is above UnicodeExtra's max and UnicodeExtra's median is below the fast median,
-- so comparing the wrong field or swapping the arguments gives false here.
/-- The pass mark is met when the fast median equals UnicodeExtra's maximum sample. -/
theorem meetsPassMark_true_at_theirs_max :
    Bench.meetsPassMark { median := 500, min := 100, max := 900, count := 3 }
      { median := 300, min := 200, max := 500, count := 3 } = true := by
  decide
