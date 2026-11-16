import Bench.Report

-- "Add a pure `Bench.meetsPassMark (fast theirs : Bench.Stats) : Bool` that is `fast.median ≤ theirs.max`."
-- The fast median equals UnicodeExtra's max. Comparing median to median (500 ≤ 300) or max to
-- max (900 ≤ 500) would give false, so only the stated rule gives true.
/-- The fast median equal to UnicodeExtra's maximum passes, even where other fields would fail. -/
theorem meets_pass_mark_true_at_max_where_wrong_fields_say_false :
    Bench.meetsPassMark { median := 500, min := 100, max := 900, count := 31 }
      { median := 300, min := 200, max := 500, count := 31 } = true := by
  decide
