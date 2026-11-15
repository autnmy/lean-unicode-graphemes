import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- Both inputs differ; the difference reported must come from the input listed first.
theorem «checkAll reports the first input in order when several inputs differ» :
    (Bench.checkAll (fun s => [s]) (fun _ => [])
        [{ name := "one", text := "p" }, { name := "two", text := "q" }]).map
        (fun d => d.input)
      = some "one" := by
  decide
