import Lean
import Segmentation

-- "Add `#guard` checks: \"\\r\\n\" is one cluster, \"a\\r\\nb\" is three clusters, an ASCII run
-- followed by a combining mark keeps the mark on the last letter, and an empty slice gives `[]`."
-- "`scanClusters` is a tail loop that pushes cluster bounds into an `Array`"
-- Expected clusters are literals, never `graphemes`, which the csimp lemma turns into the scanner.
-- The cluster count is read from the bounds array the loop fills, and the contents from
-- `sliceGraphemes`.
/-- CR LF is one cluster, a CR LF b is three, a combining mark after an ASCII run stays on the last
letter, and the empty slice has no clusters and one cut at 0. -/
theorem slice_scanner_issue_guards_cr_lf_ascii_run_mark_and_empty : True := by
  run_tac do
    let agrees (text : String) (expected : List String) : Bool :=
      let s := text.toSlice
      (Segmentation.clusterBounds s : Array (Segmentation.ClusterBounds s)).size == expected.length &&
        (Segmentation.sliceGraphemes s).map String.Slice.copy == expected
    unless agrees "\r\n" ["\r\n"] do
      throwError "\"\\r\\n\" is not one cluster"
    unless agrees "a\r\nb" ["a", "\r\n", "b"] do
      throwError "\"a\\r\\nb\" is not three clusters"
    unless agrees "xya\u0301" ["x", "y", "a\u0301"] do
      throwError "the combining mark after an ASCII run is not on the last letter"
    unless agrees "" [] do
      throwError "the empty slice does not give []"
    unless ((Segmentation.sliceBoundaries "".toSlice).map (fun p => p.offset.byteIdx)) == [0] do
      throwError "the empty slice does not have the single cut 0"
  trivial
