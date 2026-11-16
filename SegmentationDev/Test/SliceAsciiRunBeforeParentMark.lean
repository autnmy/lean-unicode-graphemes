import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- In the parent, U+0301 follows "a" and joins it (GB9). The sub-slice ends just before U+0301, so
-- the following code point is not in the slice and must not join: a run that peeks past the slice
-- end to decide whether the last letter is joined gives "a" plus a byte of the mark.
open Lean in
/-- A sub-slice that ends just before a combining mark in its parent keeps its last letter as a
cluster of its own. -/
theorem ascii_run_ending_before_parent_combining_mark_keeps_last_letter_alone : True := by
  run_tac do
    let parent := sliceTestText [0x00E9, 0x78, 0x79, 0x61, 0x0301]
    let sub := (parent.toSlice.drop 1).take 3
    unless sub.copy == "xya" do
      throwError "the sub-slice is not \"xya\""
    unless sliceAgreesWithReference sub do
      throwError "the scanner disagrees with the reference on a sub-slice ending before a mark"
    unless (Segmentation.clusterBounds sub).size == 3 do
      throwError "the scanner does not give exactly three clusters for \"xya\""
    unless (Segmentation.sliceGraphemes sub).map String.Slice.copy == ["x", "y", "a"] do
      throwError "the last letter took a code point from past the sub-slice end"
    unless (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) == [0, 1, 2, 3] do
      throwError "the cuts are not measured from the sub-slice start"
  trivial
