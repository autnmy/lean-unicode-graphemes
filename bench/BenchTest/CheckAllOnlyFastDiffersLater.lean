import Bench.Compare

-- "The check fails naming the input when only the fast list differs, when only this library's
-- differs, and when only UnicodeExtra's differs, and passes when all agree, by tests in
-- `bench/BenchTest/`."
-- The first input agrees, so a check that always names the first input fails here, and the
-- odd value must sit in the `fast` field, not in `ours`.
/-- When only the fast list differs on the second input, the check names that input and the fast cluster. -/
theorem check_all_names_later_input_when_only_fast_differs :
    Bench.checkAll (fun text => [text]) (fun text => [text])
        (fun text => if text = "bbb" then ["b", "bb"] else [text])
        [{ name := "first", text := "a" }, { name := "second", text := "bbb" }] =
      some { input := "second", index := 0, ours := some "bbb", theirs := some "bbb",
             fast := some "b" } := by
  decide
