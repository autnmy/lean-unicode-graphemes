import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- Both parents start with U+00E9 (2 bytes), so each sub-slice starts at byte 2. The first ends
-- inside an ASCII run that continues in the parent; the second ends just before a combining mark
-- in the parent, so its last letter must not take that mark. Cuts are byte offsets from the
-- sub-slice start.
/-- On sub-slices that start after byte 0 and end inside or just before more text of the parent,
the scanner reads only the sub-slice and its cuts count from the sub-slice start. -/
theorem ascii_run_on_sub_slice_stops_at_slice_end_and_measures_from_slice_start : True := by
  run_tac do
    let inRun := ((sliceTestText [0x00E9, 0x78, 0x79, 0x7A, 0x77, 0x76]).toSlice.drop 1).take 3
    unless inRun.copy == "xyz" && sliceAgreesWithReference inRun &&
        (Segmentation.sliceGraphemes inRun).map String.Slice.copy == ["x", "y", "z"] &&
        (Segmentation.sliceBoundaries inRun).map (fun p => p.offset.byteIdx) == [0, 1, 2, 3] &&
        (Segmentation.clusterBounds inRun : Array (Segmentation.ClusterBounds inRun)).size == 3 do
      throwError "a sub-slice ending inside an ASCII run is not segmented on its own bytes"
    let beforeMark := ((sliceTestText [0x00E9, 0x78, 0x79, 0x61, 0x0301]).toSlice.drop 1).dropEnd 1
    unless beforeMark.copy == "xya" && sliceAgreesWithReference beforeMark &&
        (Segmentation.sliceGraphemes beforeMark).map String.Slice.copy == ["x", "y", "a"] &&
        (Segmentation.sliceBoundaries beforeMark).map (fun p => p.offset.byteIdx) == [0, 1, 2, 3] &&
        (Segmentation.clusterBounds beforeMark :
          Array (Segmentation.ClusterBounds beforeMark)).size == 3 do
      throwError "a sub-slice ending before a combining mark joins the mark past its end"
  trivial
