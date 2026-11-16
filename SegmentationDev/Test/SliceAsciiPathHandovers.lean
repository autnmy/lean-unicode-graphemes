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

-- U+0600 is Prepend. The first ASCII byte after it is where the run starts, and the decision there
-- depends on the non-ASCII code point before it: GB9b joins a letter to it, and GB5 breaks before
-- CR. A run that treats its first byte like the bytes inside the run cuts after U+0600 in both.
open Lean in
/-- A Prepend code point joins the ASCII letter after it, but not a CR LF after it. -/
theorem prepend_before_ascii_run_joins_letter_but_not_cr_lf : True := by
  run_tac do
    let joined := (sliceTestText [0x0600, 0x61, 0x62]).toSlice
    unless (Segmentation.clusterBounds joined).size == 2 do
      throwError "Prepend then \"ab\" is not two clusters"
    let split := (sliceTestText [0x0600, 0x0D, 0x0A, 0x61]).toSlice
    unless sliceAgreesWithReference split do
      throwError "the scanner disagrees with the reference on Prepend then CR LF"
    unless (Segmentation.clusterBounds split).size == 3 do
      throwError "Prepend then CR LF then a is not three clusters"
    unless (Segmentation.sliceGraphemes split).map String.Slice.copy == ["\u0600", "\r\n", "a"] do
      throwError "Prepend joined a CR, or CR LF was split"
  trivial

-- U+0080 and U+0085 are controls encoded in two bytes each (0xC2 0x80, 0xC2 0x85). A run test that
-- takes any byte below 0x100, or a continuation byte, as ASCII would step one byte into a code point
-- and cut inside it, which moves every later byte cut.
open Lean in
/-- Two-byte controls between ASCII bytes and a CR LF stay whole clusters, cut on code-point
boundaries. -/
theorem two_byte_controls_between_ascii_are_not_read_as_ascii : True := by
  run_tac do
    let s := (sliceTestText [0x61, 0x0080, 0x0D, 0x0A, 0x0085, 0x62]).toSlice
    unless sliceAgreesWithReference s do
      throwError "the scanner disagrees with the reference around two-byte controls"
    unless (Segmentation.clusterBounds s).size == 5 do
      throwError "a, U+0080, CR LF, U+0085, b is not five clusters"
    unless (Segmentation.sliceBoundaries s).map (fun p => p.offset.byteIdx) == [0, 1, 3, 5, 7, 8] do
      throwError "a cut falls inside a two-byte code point"
  trivial
