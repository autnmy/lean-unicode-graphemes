import Bench.Compare

-- "The check fails naming the input when only the fast list differs, when only this library's
-- differs, and when only UnicodeExtra's differs, and passes when all agree."
-- The first input agrees, so the check must name the second one, not just the first.
/-- When only the fast list differs on the second input, the check names that input and puts the odd cluster in the fast field. -/
theorem checkAll_names_input_when_only_fast_differs :
    ((Bench.checkAll (fun t => [t]) (fun t => [t]) (fun t => if t = "b" then ["x"] else [t])
        ([{ name := "first", text := "a" }, { name := "second", text := "b" }] :
          List Bench.NamedInput)).map
      (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))) =
    some ("second", 0, some "b", some "b", some "x") := by
  decide
