import Lean
import Segmentation

-- "The scanner reuses `ScanState`, `ScanState.start`, `ScanState.push` and `breaksBefore` from
-- `Segmentation/Graphemes.lean` unchanged."
-- If the ASCII path skips pushing its code points into the scan state, flags from before the run
-- survive it: U+1F469 U+200D leaves the GB11 flag set, so "a" then U+1F469 would wrongly join; and
-- an odd regional indicator before "a" would wrongly pair the next two indicators differently.
-- Each input must give exactly the reference's clusters and byte cuts.
open Lean Elab Command in
theorem «ASCII run between emoji ZWJ and regional indicator state clears the state as the reference does» :
    True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    modifyThe Core.State fun st => { st with messages := {} }
    liftCommandElabM (elabCommand (← `(command|
      #guard
        [[0x1F469, 0x200D, 0x61, 0x1F469],
         [0x1F469, 0x200D, 0x1F469, 0x61, 0x62, 0x1F469, 0x200D, 0x1F469],
         [0x1F1E6, 0x61, 0x1F1E7, 0x1F1E8],
         [0x78, 0x1F1E6, 0x1F1E7]].all fun cps =>
          let s := String.ofList (cps.map Char.ofNat)
          (Segmentation.sliceGraphemes s.toSlice).map String.Slice.copy == Segmentation.graphemes s &&
          (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) ==
            (Segmentation.boundaries s).map
              (fun n => (String.ofList (s.toList.take n)).utf8ByteSize))))
    let errors ← ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).mapM (·.toString)
    modifyThe Core.State fun st => { st with messages := saved }
    unless errors.isEmpty do
      throwError "state left over from before an ASCII run changed a cut: {errors}"
  trivial
