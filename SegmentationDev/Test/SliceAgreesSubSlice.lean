import Lean
import Segmentation

-- "A sub-slice taken from the middle of a larger string must return slices of that sub-slice and
-- cuts measured from its start."
-- The parent is U+00E9 (2 bytes), "x", U+0301, CR, LF, "z". The sub-slice drops the first and the
-- last two code points, so it starts at byte 2 and ends on the CR, with the parent's LF just past
-- its end. Cuts measured from the parent would read [2, 5, 6]; a scan that reads past the end would
-- join the CR to the LF.
open Lean Elab Command in
theorem «slice_scanner_on_mid_string_sub_slice_cuts_from_its_own_start» : True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    liftCommandElabM (elabCommand (← `(command|
      #guard
        let parent := String.ofList ([0x00E9, 0x78, 0x0301, 0x0D, 0x0A, 0x7A].map Char.ofNat)
        let sub := (parent.toSlice.drop 1).dropEnd 2
        let copied := sub.copy
        copied == "x\u0301\r" &&
          (Segmentation.sliceGraphemes sub).map String.Slice.copy ==
            Segmentation.graphemes copied &&
          (Segmentation.sliceGraphemes sub).map String.Slice.copy == ["x\u0301", "\r"] &&
          (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) ==
            (Segmentation.boundaries copied).map
              (fun n => (String.ofList (copied.toList.take n)).utf8ByteSize) &&
          (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) == [0, 3, 4])))
    let failed := (← getThe Core.State).messages.hasErrors
    modifyThe Core.State fun s => { s with messages := saved }
    if failed then
      throwError "the slice scanner is wrong on a sub-slice from the middle of a string"
  trivial
