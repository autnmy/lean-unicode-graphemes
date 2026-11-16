import Lean
import Segmentation

-- "`scanClusters` is a tail loop that pushes cluster bounds into an `Array`, and
-- `sliceGraphemes_agree` and both `@[csimp]` lemmas still prove."
-- The scan must take an `Array` accumulator and return an `Array`, and `clusterBounds` must hand
-- that `Array` on, so a scan that conses onto a returned `List` fails here.
open Lean in
/-- The slice scan takes and returns an Array of cluster bounds, and clusterBounds returns that Array. -/
theorem slice_scan_clusters_accumulates_bounds_in_array : True := by
  run_tac do
    let env ← getEnv
    for (name, needsAccumulator) in
        [(``Segmentation.scanClusters, true), (``Segmentation.clusterBounds, false)] do
      let some info := env.find? name | throwError m!"{name} is missing"
      unless info matches .defnInfo _ do
        throwError m!"{name} is not a plain definition"
      let (returnsArray, takesArray) ← Meta.forallTelescope info.type fun xs body => do
        let takesArray ← xs.anyM fun x =>
          return (← Meta.inferType x).getAppFn.isConstOf ``Array
        return (body.getAppFn.isConstOf ``Array, takesArray)
      unless returnsArray do
        throwError m!"{name} does not return an Array of cluster bounds"
      if needsAccumulator && !takesArray then
        throwError m!"{name} takes no Array accumulator"
  trivial

-- The scan lemma must speak about the Array the new loop accumulates into, so the old List
-- statement fails here. The axioms of the agreement theorems are checked by `#assert_axioms` in
-- `SegmentationDev/Test/SliceAsciiPath.lean`.
open Lean in
/-- The scan agreement is stated over the Array accumulator. -/
theorem scan_clusters_agree_is_stated_over_array_accumulator : True := by
  run_tac do
    let some agree := (← getEnv).find? ``Segmentation.scanClusters_agree
      | throwError "scanClusters_agree is missing"
    unless agree.type.getUsedConstants.any (fun c => (`Array).isPrefixOf c) do
      throwError "scanClusters_agree is not stated over the Array the scan accumulates into"
  trivial
