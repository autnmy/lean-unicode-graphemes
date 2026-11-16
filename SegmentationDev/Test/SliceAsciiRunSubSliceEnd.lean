import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- The parent starts with U+00E9 (2 bytes), so the sub-slice starts at byte 2, and its ASCII run
-- goes on in the parent past the sub-slice end. A run that reads bytes from the parent's start,
-- or stops at the parent's end instead of the slice's, gives more clusters or shifted cuts.
open Lean in
/-- A sub-slice that starts at byte 2 and ends inside an ASCII run of its parent gives one
cluster per letter, cut at byte offsets from its own start, and no more. -/
theorem ascii_run_stops_at_sub_slice_end_inside_parent_run : True := by
  run_tac do
    let parent := sliceTestText [0x00E9, 0x61, 0x62, 0x63, 0x64, 0x65]
    let sub := (parent.toSlice.drop 1).take 3
    unless sub.copy == "abc" do
      throwError "the sub-slice is not \"abc\""
    unless sliceAgreesWithReference sub do
      throwError "the scanner disagrees with the reference on a sub-slice inside an ASCII run"
    unless (Segmentation.clusterBounds sub).size == 3 do
      throwError "the scanner does not give exactly three clusters for \"abc\""
    unless (Segmentation.sliceGraphemes sub).map String.Slice.copy == ["a", "b", "c"] do
      throwError "the clusters of the sub-slice are not a, b, c"
    unless (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) == [0, 1, 2, 3] do
      throwError "the cuts are not measured from the sub-slice start"
  trivial
