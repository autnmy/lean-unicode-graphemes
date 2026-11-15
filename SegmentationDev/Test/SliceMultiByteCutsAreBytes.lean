import Lean
import Segmentation

-- "The byte position of code-point cut n is the UTF-8 size of the first n code points of `s`."
-- U+00E9 is 2 bytes, U+4E2D is 3 bytes and U+1F600 is 4 bytes. A scanner that steps one byte per
-- code point, or reports code-point counts, or treats a continuation byte as ASCII, gives different
-- cuts. The last input puts CR LF right where an ASCII run meets a non-ASCII code point.
open Lean Elab Command in
theorem «multi-byte code points at the start and end give byte cuts not code point cuts» :
    True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    modifyThe Core.State fun st => { st with messages := {} }
    liftCommandElabM (elabCommand (← `(command|
      #guard
        (let s := String.ofList ([0x00E9, 0x4E2D, 0x1F600].map Char.ofNat)
         (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) == [0, 2, 5, 9]) &&
        [[0x00E9, 0x4E2D, 0x1F600], [0x1F600, 0x61, 0x62, 0x00E9], [0x61, 0x62, 0x0D, 0x0A, 0x4E2D],
         [0x4E2D, 0x0D, 0x0A, 0x61]].all fun cps =>
          let s := String.ofList (cps.map Char.ofNat)
          (Segmentation.sliceGraphemes s.toSlice).map String.Slice.copy == Segmentation.graphemes s &&
          (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) ==
            (Segmentation.boundaries s).map
              (fun n => (String.ofList (s.toList.take n)).utf8ByteSize))))
    let errors ← ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).mapM (·.toString)
    modifyThe Core.State fun st => { st with messages := saved }
    unless errors.isEmpty do
      throwError "byte cuts disagree with the reference on multi-byte input: {errors}"
  trivial
