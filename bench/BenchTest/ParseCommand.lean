import Lean
import Main

/-!
These checks import `Main`, which defines `main`, so the test driver `BenchTest` cannot import
this module. Building the `BenchChecks` library elaborates it, and so runs every check here.
-/

-- "`Library` in `bench/Bench/Measure.lean` gains a `.fast` case, named \"fast\", in
-- `Library.all`, `Library.name` and `clusterCountOf` in `bench/Main.lean`."
-- The fast and reference counts are equal on every input, so only the definition shows which
-- counter the fast child process times. This walk fails unless `clusterCountOf` names
-- `Bench.fastClusterCount`, and the `.fast` arm is the only one that can.
open Lean in
theorem clusterCountOf_reaches_fastClusterCount : True := by
  run_tac do
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Bench.clusterCountOf]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if seen.contains n then continue
      seen := seen.insert n
      if (`Bench.clusterCountOf).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do
            todo := todo.push c
        | some _ => pure ()
        | none => throwError m!"{n} is missing"
    unless seen.contains ``Bench.fastClusterCount do
      throwError m!"Bench.clusterCountOf does not use Bench.fastClusterCount"
  trivial

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
