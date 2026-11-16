import Bench.Compare

-- "The check fails naming the input when only the fast list differs, when only this library's
-- differs, and when only UnicodeExtra's differs, and passes when all agree."
/-- When all three segmenters return the same clusters on every input, the check finds no difference. -/
theorem checkAll_passes_when_all_three_agree :
    (Bench.checkAll (fun t => [t, ""]) (fun t => [t, ""]) (fun t => [t, ""])
        ([{ name := "first", text := "a" }, { name := "second", text := "b" }] :
          List Bench.NamedInput)).isNone = true := by
  decide
