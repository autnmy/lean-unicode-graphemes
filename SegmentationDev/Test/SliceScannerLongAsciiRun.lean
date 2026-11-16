import Lean
import Segmentation

-- "`scanClusters` is a tail loop that pushes cluster bounds into an `Array`"
-- One million ASCII letters are one million clusters; a scan that conses onto its own recursive
-- call goes one call deep per cluster. The final U+0301 must stay on the last letter.
/-- A million ASCII letters followed by a combining mark give a million clusters, the last one the
letter with its mark, and the scan loop returns them as an array. -/
theorem scan_clusters_handles_a_million_ascii_clusters_then_a_mark : True := by
  run_tac do
    let count := 1000000
    let text := String.ofList (List.replicate count 'a') ++ "\u0301"
    let s := text.toSlice
    let bounds : Array (Segmentation.ClusterBounds s) := Segmentation.clusterBounds s
    unless bounds.size == count do
      throwError m!"expected {count} cluster bounds, got {bounds.size}"
    let clusters := Segmentation.sliceGraphemes s
    unless clusters.length == count do
      throwError m!"expected {count} clusters, got {clusters.length}"
    unless clusters.getLast?.map String.Slice.copy == some "a\u0301" do
      throwError "the combining mark is not on the last letter"
  trivial
