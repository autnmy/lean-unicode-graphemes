import Bench.Report

-- "Add a pure `Bench.meetsPassMark (fast theirs : Bench.Stats) : Bool` that is `fast.median ≤ theirs.max`."
-- The fast median is below UnicodeExtra's min, but the fast max is above UnicodeExtra's max, so a
-- rule that compared the two maximums would give false here.
/-- A fast median below UnicodeExtra's whole spread meets the pass mark. -/
theorem meetsPassMark_true_below_theirs_min :
    Bench.meetsPassMark { median := 150, min := 100, max := 900, count := 3 }
      { median := 300, min := 200, max := 500, count := 3 } = true := by
  decide
