import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
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
