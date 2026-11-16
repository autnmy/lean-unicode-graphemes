import Bench.Compare

-- "The check fails naming the input when only the fast list differs, when only this library's
-- differs, and when only UnicodeExtra's differs, and passes when all agree."
/-- When only UnicodeExtra's list differs on the second input, the check names that input and puts the odd cluster in the theirs field. -/
theorem checkAll_names_input_when_only_theirs_differs :
    ((Bench.checkAll (fun t => [t]) (fun t => if t = "b" then ["x"] else [t]) (fun t => [t])
        ([{ name := "first", text := "a" }, { name := "second", text := "b" }] :
          List Bench.NamedInput)).map
      (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))) =
    some ("second", 0, some "b", some "x", some "b") := by
  decide
