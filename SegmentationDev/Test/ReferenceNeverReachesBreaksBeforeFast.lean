import Lean
import Segmentation

-- "The benchmark's reference column, `Bench.oursClusters` and `Bench.oursClusterCount` in
-- `bench/Bench/Libraries.lean`, must never reach `breaksBeforeFast`."
-- The reference column runs `Segmentation.clustersOf`. This walk follows every `Segmentation`
-- definition that `clustersOf`, `breaksBefore` and `breakRows` use. It fails if the walk reaches
-- the fast decision, for example after an edit that makes `breaksBefore` call it. It also fails
-- if `breaksBeforeFast` is missing, so it cannot pass before the change exists.
/-- The reference `clustersOf`, `breaksBefore` and `breakRows` never reach `breaksBeforeFast`. -/
theorem reference_clusters_of_never_reaches_breaks_before_fast : True := by
  run_tac do
    let env ← Lean.getEnv
    unless env.contains ``Segmentation.breaksBeforeFast do
      throwError "Segmentation.breaksBeforeFast is missing"
    let mut seen : Lean.NameSet := {}
    let mut todo : Array Lean.Name :=
      #[``Segmentation.clustersOf, ``Segmentation.breaksBefore, ``Segmentation.breakRows]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if n == ``Segmentation.breaksBeforeFast then
        throwError m!"the reference reaches {n}, the scanner's fast decision"
      if seen.contains n then continue
      seen := seen.insert n
      if (`Segmentation).isPrefixOf n then
        match env.find? n with
        | some (.defnInfo info) =>
          for c in info.value.getUsedConstants do
            todo := todo.push c
        | _ => pure ()
  trivial
