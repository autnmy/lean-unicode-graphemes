import Bench.Report

/-!
Checks of `Bench.meetsPassMark`, which the issue states as: "Add a pure
`Bench.meetsPassMark (fast theirs : Bench.Stats) : Bool` that is `fast.median ≤ theirs.max`."
Each fixture gives UnicodeExtra a different median, min and max, so a rule that read the wrong
field, or took the arguments the other way round, gives the opposite answer somewhere below.
-/

-- The fast max is above UnicodeExtra's max and UnicodeExtra's median is below the fast median,
-- so comparing the wrong field or swapping the arguments gives false here.
/-- The pass mark is met when the fast median equals UnicodeExtra's maximum sample. -/
theorem meetsPassMark_true_at_theirs_max :
    Bench.meetsPassMark { median := 500, min := 100, max := 900, count := 3 }
      { median := 300, min := 200, max := 500, count := 3 } = true := by
  decide

-- "`meetsPassMark` passes at equality with UnicodeExtra's max and fails one nanosecond above"
-- The fast min is below every UnicodeExtra figure, so a rule that read the fast min would pass.
/-- The pass mark is missed when the fast median is one nanosecond above UnicodeExtra's maximum sample. -/
theorem meetsPassMark_false_one_ns_above_theirs_max :
    Bench.meetsPassMark { median := 501, min := 100, max := 600, count := 3 }
      { median := 300, min := 200, max := 500, count := 3 } = false := by
  decide

-- The fast median is 501 against a max of 500. Median to median (501 ≤ 600) and swapped
-- arguments (600 ≤ 700) would both give true, so only the stated rule gives false.
/-- A fast median one nanosecond above UnicodeExtra's maximum fails the pass mark. -/
theorem meets_pass_mark_false_one_above_max_where_wrong_rules_say_true :
    Bench.meetsPassMark { median := 501, min := 100, max := 700, count := 31 }
      { median := 600, min := 200, max := 500, count := 31 } = false := by
  decide

-- The fast median is below UnicodeExtra's min, but the fast max is above UnicodeExtra's max, so a
-- rule that compared the two maximums would give false here.
/-- A fast median below UnicodeExtra's whole spread meets the pass mark. -/
theorem meetsPassMark_true_below_theirs_min :
    Bench.meetsPassMark { median := 150, min := 100, max := 900, count := 3 }
      { median := 300, min := 200, max := 500, count := 3 } = true := by
  decide
