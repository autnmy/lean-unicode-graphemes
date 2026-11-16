import Lean
import Segmentation
import SegmentationDev.Test.SliceAgreesEdgeInputs

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- U+0600 is Prepend. The first ASCII byte after it is where the run starts, and the decision there
-- depends on the non-ASCII code point before it: GB9b joins a letter to it, and GB5 breaks before
-- CR. A run that treats its first byte like the bytes inside the run cuts after U+0600 in both.
open Lean in
/-- A Prepend code point joins the ASCII letter after it, but not a CR LF after it. -/
theorem prepend_before_ascii_run_joins_letter_but_not_cr_lf : True := by
  run_tac do
    let joined := (sliceTestText [0x0600, 0x61, 0x62]).toSlice
    unless sliceAgreesWithReference joined do
      throwError "the scanner disagrees with the reference on Prepend then an ASCII run"
    unless (Segmentation.clusterBounds joined).size == 2 do
      throwError "Prepend then \"ab\" is not two clusters"
    unless (Segmentation.sliceGraphemes joined).map String.Slice.copy == ["\u0600a", "b"] do
      throwError "Prepend did not join the first letter of the ASCII run"
    let split := (sliceTestText [0x0600, 0x0D, 0x0A, 0x61]).toSlice
    unless sliceAgreesWithReference split do
      throwError "the scanner disagrees with the reference on Prepend then CR LF"
    unless (Segmentation.clusterBounds split).size == 3 do
      throwError "Prepend then CR LF then a is not three clusters"
    unless (Segmentation.sliceGraphemes split).map String.Slice.copy == ["\u0600", "\r\n", "a"] do
      throwError "Prepend joined a CR, or CR LF was split"
  trivial
