import Lean
import Segmentation

-- "`scanClusters` is a tail loop that pushes cluster bounds into an `Array`"
-- A loop with a step budget, or one that recurses once per cluster, fails on a long input: the
-- first drops the clusters past its budget, the second runs out of stack. Three hundred thousand
-- ASCII letters then U+0301 must give one cluster per letter, with the mark on the last one.
open Lean in
/-- A run of 300000 ASCII letters followed by a combining mark gives 300000 clusters, the last
being the letter with its mark. -/
theorem long_ascii_run_then_mark_keeps_every_cluster : True := by
  run_tac do
    let text := String.ofList (List.replicate 300000 'a' ++ ['\u0301'])
    let s := text.toSlice
    unless (Segmentation.clusterBounds s).size == 300000 do
      throwError "the scanner did not give one cluster per letter on a long ASCII run"
    unless (Segmentation.sliceGraphemes s).getLast?.map String.Slice.copy == some "a\u0301" do
      throwError "the last letter of a long ASCII run did not keep the combining mark"
    unless (Segmentation.sliceBoundaries s).getLast?.map (fun p => p.offset.byteIdx) ==
        some 300002 do
      throwError "the last cut of a long ASCII run is not the end of the text"
  trivial
