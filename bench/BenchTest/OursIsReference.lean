import Lean
import Bench.Libraries

-- "In `bench/Bench/Libraries.lean`, neither `oursClusters` nor `oursClusterCount` calls
-- `Segmentation.graphemes`, and `oursClusterCount` counts `oursClusters`' result."
-- After csimp, compiled `Segmentation.graphemes` runs the fast scanner and returns the same
-- clusters, so only the definitions themselves can show the column still runs the reference.
-- The walk follows names in `Bench`, so a call through a local helper is caught too.
open Lean in
theorem «the benchmark's reference column never calls Segmentation.graphemes» : True := by
  run_tac do
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Bench.oursClusters, ``Bench.oursClusterCount]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if n == ``Segmentation.graphemes then
        throwError m!"the benchmark's reference column calls {n}, which csimp sends to the fast scanner"
      if seen.contains n then continue
      seen := seen.insert n
      if (`Bench).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do
            todo := todo.push c
        | some _ => pure ()
        | none => throwError m!"{n} is missing"
    match env.find? ``Bench.oursClusterCount with
    | some (.defnInfo info) =>
      unless info.value.getUsedConstants.contains ``Bench.oursClusters do
        throwError m!"Bench.oursClusterCount does not count Bench.oursClusters' result"
    | _ => throwError m!"Bench.oursClusterCount is not a plain definition"
  trivial

#guard Bench.oursClusters "a\u0301b" == ["a\u0301", "b"]
#guard Bench.oursClusterCount "a\u0301b" == 2
