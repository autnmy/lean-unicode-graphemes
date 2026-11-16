import Lean
import Segmentation

-- "Make `scanClusters` push a caller-chosen element per cluster so `sliceGraphemes` builds its
-- slices in the scan instead of allocating a `ClusterBounds` per cluster first."
-- The clusters are the same either way, so only a walk over definition bodies can see it. The walk
-- must reach the scan, so it cannot pass by walking nothing, and must reach neither the
-- `ClusterBounds` constructor nor `Array.foldr`, the two marks of building the bounds first and the
-- list from them in a second pass.
open Lean in
/-- `sliceGraphemes` reaches the scan but neither builds cluster bounds nor folds an array of them. -/
theorem slice_graphemes_scan_emits_slices_without_bounds : True := by
  run_tac do
    let env ← getEnv
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[``Segmentation.sliceGraphemes]
    let mut i := 0
    while i < todo.size do
      let n := todo[i]!
      i := i + 1
      if seen.contains n then continue
      seen := seen.insert n
      if (`Segmentation).isPrefixOf n then
        if let some (.defnInfo info) := env.find? n then
          for c in info.value.getUsedConstants do
            todo := todo.push c
    unless seen.contains ``Segmentation.scanClusters do
      throwError "Segmentation.sliceGraphemes does not reach Segmentation.scanClusters"
    for twoPass in [``Segmentation.ClusterBounds.mk, ``Array.foldr] do
      if seen.contains twoPass then
        throwError m!"Segmentation.sliceGraphemes reaches {twoPass}"
  trivial
