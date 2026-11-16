import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- Each input puts an ASCII run against the place where it hands over to the full decision: a
-- Prepend (U+0600) before a letter, a letter before a SpacingMark (U+0903) or a ZWJ, a lone CR at
-- the end, LF then CR, and an ASCII run between two regional indicators. Expected values come from
-- the reference `clustersOf` and `cutsOf`, plus literal clusters for the Prepend case.
/-- At every place an ASCII run meets the full break decision, the scanner's clusters and byte
cuts equal the reference, and its bounds come back as an array. -/
theorem ascii_path_handovers_agree_with_reference : True := by
  run_tac do
    let inputs : List (List Nat) := [
      [0x0600, 0x61, 0x62],
      [0x61, 0x62, 0x0903],
      [0x61, 0x62, 0x200D, 0x63],
      [0x61, 0x62, 0x0D],
      [0x0A, 0x0D, 0x61],
      [0x1F1E6, 0x61, 0x62, 0x1F1E7, 0x1F1E8]]
    for cps in inputs do
      let s := (sliceTestText cps).toSlice
      unless sliceAgreesWithReference s do
        throwError m!"the scanner disagrees with the reference on {cps}"
      unless (Segmentation.clusterBounds s : Array (Segmentation.ClusterBounds s)).size ==
          (Segmentation.sliceGraphemes s).length do
        throwError m!"the bounds array and the cluster list differ in length on {cps}"
    let prepend := (sliceTestText [0x0600, 0x61, 0x62]).toSlice
    unless (Segmentation.sliceGraphemes prepend).map String.Slice.copy ==
        [sliceTestText [0x0600, 0x61], "b"] do
      throwError "a Prepend does not join the ASCII letter after it"
  trivial
