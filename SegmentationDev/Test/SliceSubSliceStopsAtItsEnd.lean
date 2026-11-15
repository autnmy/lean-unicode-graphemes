import Lean
import Segmentation

-- "A sub-slice taken from the middle of a larger string must return slices of that sub-slice and
-- cuts measured from its start."
-- The parent is U+00E9 (two bytes), "x", "a", CR, LF, "b". The sub-slice drops U+00E9 and keeps
-- "xa" then CR, so it starts at byte 2 and its CR has an LF just past its end. A scanner that reads
-- past the slice end joins CR with that LF (GB3); one that measures from the parent's start gives
-- cuts shifted by 2. Expected values come only from the reference on the sub-slice's own text.
open Lean Elab Command in
theorem «sub-slice ending in CR before an outside LF keeps its own cuts and does not read past its end» :
    True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    modifyThe Core.State fun st => { st with messages := {} }
    liftCommandElabM (elabCommand (← `(command|
      #guard
        let parent := String.ofList ([0x00E9, 0x78, 0x61, 0x0D, 0x0A, 0x62].map Char.ofNat)
        let sub := (parent.toSlice.drop 1).take 3
        let t := sub.copy
        t == String.ofList ([0x78, 0x61, 0x0D].map Char.ofNat) &&
        (Segmentation.sliceGraphemes sub).map String.Slice.copy == Segmentation.graphemes t &&
        (Segmentation.sliceGraphemes sub).map String.Slice.copy ==
          [String.ofList [Char.ofNat 0x78], String.ofList [Char.ofNat 0x61],
            String.ofList [Char.ofNat 0x0D]] &&
        (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) ==
          (Segmentation.boundaries t).map (fun n => (String.ofList (t.toList.take n)).utf8ByteSize) &&
        (Segmentation.sliceBoundaries sub).map (fun p => p.offset.byteIdx) == [0, 1, 2, 3])))
    let errors ← ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).mapM (·.toString)
    modifyThe Core.State fun st => { st with messages := saved }
    unless errors.isEmpty do
      throwError "the sub-slice scan disagrees with the reference: {errors}"
  trivial
