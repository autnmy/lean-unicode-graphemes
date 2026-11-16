import Main

/-!
These checks import `Main`, which defines `main`, so the test driver `BenchTest` cannot import
this module. Building the `BenchChecks` library elaborates it, and so runs every check here.
-/

-- "`--break-ours` drops the last cluster of this library's list only, and `--break-fast` drops the
-- last cluster of the fast list only."
/-- The break-fast flag parses to a check that breaks the fast list, and the break-ours flag still breaks this library's list. -/
theorem parseCommand_break_fast_breaks_fast_only :
    ((match Bench.parseCommand ["check", "--break-fast"] with
      | some (.check (some .fast)) => true
      | _ => false) &&
     (match Bench.parseCommand ["check", "--break-ours"] with
      | some (.check (some .ours)) => true
      | _ => false) &&
     (match Bench.parseCommand ["check"] with
      | some (.check none) => true
      | _ => false)) = true := by
  decide

-- `Command.check` holds one broken library, so an argument list with two flags, a repeated
-- flag or an unknown flag must not parse; parsing it as an unbroken check would exit 0 on a typo.
/-- Two break flags, a repeated flag and an unknown break flag are all rejected by the parser. -/
theorem parse_command_rejects_combined_or_unknown_break_flags :
    ((Bench.parseCommand ["check", "--break-ours", "--break-fast"]).isNone &&
      (Bench.parseCommand ["check", "--break-fast", "--break-fast"]).isNone &&
      (Bench.parseCommand ["check", "--break-theirs"]).isNone &&
      (Bench.parseCommand ["check", "--break-fast"]).isSome) = true := by
  decide

-- `measure fast <input>` parses to a measurement of the fast library, because `Library` gains a
-- `.fast` case named "fast" in `Library.all` and `Library.name`; an unknown library name still
-- fails to parse.
#guard
    ((match Bench.parseCommand ["measure", "fast", "emoji"] with
      | some (.measure .fast _) => true
      | _ => false) &&
     (Bench.Library.all.contains .fast) &&
     (Bench.Library.name .fast == "fast") &&
     (Bench.parseCommand ["measure", "quick", "emoji"]).isNone)

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

-- The fast and reference counts are equal on every input, so only the definition shows which
-- counter each child process times. Each arm is pinned, so swapping two of them fails here.
theorem clusterCountOf_fast_is_fastClusterCount :
    Bench.clusterCountOf .fast = some Bench.fastClusterCount := rfl
theorem clusterCountOf_ours_is_oursClusterCount :
    Bench.clusterCountOf .ours = some Bench.oursClusterCount := rfl
theorem clusterCountOf_theirs_is_theirsClusterCount :
    Bench.clusterCountOf .theirs = some Bench.theirsClusterCount := rfl

-- `--break-fast` drops a cluster from the fast list only.
#guard Bench.clustersFor (some .fast) .fast (fun _ => ["a", "b"]) "" == ["a"]
#guard Bench.clustersFor (some .fast) .ours (fun _ => ["a", "b"]) "" == ["a", "b"]
#guard Bench.clustersFor none .fast (fun _ => ["a", "b"]) "" == ["a", "b"]

-- "`describeDifference` prints three labelled lines": one per segmenter, under the first line.
#guard
  let lines := (Bench.describeDifference
    { input := "emoji", index := 2, ours := some "x", theirs := some "y", fast := some "z" }
    ).splitOn "\n"
  lines.length == 4 &&
    ((lines.getD 1 "").splitOn "lean-unicode-graphemes: \"x\"").length > 1 &&
    ((lines.getD 2 "").splitOn "UnicodeExtra:").length > 1 &&
    ((lines.getD 2 "").splitOn "\"y\"").length > 1 &&
    ((lines.getD 3 "").splitOn "fast (sliceGraphemes):").length > 1 &&
    ((lines.getD 3 "").splitOn "\"z\"").length > 1

-- Its first line keeps the words "clusters differ on input" and names the input, and a list
-- that has ended is shown as such.
#guard
  let lines := (Bench.describeDifference
    { input := "emoji", index := 2, ours := some "a", theirs := some "a", fast := none }
    ).splitOn "\n"
  lines.length == 4 &&
    ((lines.headD "").splitOn "clusters differ on input").length > 1 &&
    ((lines.headD "").splitOn "emoji").length > 1 &&
    ((lines.getD 3 "").splitOn "(no cluster: the list has ended)").length > 1
