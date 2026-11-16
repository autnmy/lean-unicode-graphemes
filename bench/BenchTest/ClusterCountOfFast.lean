import Main

-- "`Library` in `bench/Bench/Measure.lean` gains a `.fast` case, named \"fast\", in
-- `Library.all`, `Library.name` and `clusterCountOf` in `bench/Main.lean`."
-- If `.fast` mapped to `none`, its child process would time nothing, as the baseline does,
-- and the report would show an empty fast column; if "fast" did not parse, `measure fast`
-- would print usage instead of measuring.
/-- The fast library parses from the name "fast" and its child process times a counter. -/
theorem cluster_count_of_fast_times_a_counter_and_parses_by_name :
    (Bench.Library.ofName? "fast" == some Bench.Library.fast &&
      Bench.Library.name .fast == "fast" &&
      (Bench.clusterCountOf .fast).isSome &&
      (Bench.clusterCountOf .baseline).isNone) = true := by
  decide
