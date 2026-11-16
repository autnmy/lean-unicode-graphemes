import Bench.Compare

-- "checks that both return the same clusters on every input before timing, and fails with the first difference if they do not"
-- A check that stops after the first input, or reports the wrong input's name, would miss this.
theorem «checkAll names the later input when only that input differs» :
    (Bench.checkAll (fun s => [s]) (fun s => if s = "bbb" then [] else [s]) (fun s => [s])
        [{ name := "first", text := "aaa" }, { name := "second", text := "bbb" }]).map
        (fun d => (d.input, d.index, d.ours, d.theirs, d.fast))
      = some ("second", 0, some "bbb", none, some "bbb") := by
  decide
