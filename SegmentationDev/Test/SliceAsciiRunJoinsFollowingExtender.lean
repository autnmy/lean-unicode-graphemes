import Lean
import Segmentation

-- "an ASCII fast path: a run of ASCII bytes needs no table lookup except where GB3 (CR LF) or a
-- following non-ASCII code point can join it"
-- A fast path that cuts after every ASCII code point except CR before LF splits "a" from U+0301
-- (Extend), U+200D (ZWJ) and U+0903 (SpacingMark). Each input must give exactly the reference's
-- clusters and byte cuts, and its last cluster must be the extender joined to the ASCII code point
-- just before it.
open Lean Elab Command in
theorem «ASCII code point followed by a non-ASCII extender is not cut before the extender» :
    True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    modifyThe Core.State fun st => { st with messages := {} }
    liftCommandElabM (elabCommand (← `(command|
      #guard
        [[0x61, 0x0301], [0x61, 0x200D], [0x61, 0x0903], [0x78, 0x79, 0x61, 0x0301]].all fun cps =>
          let s := String.ofList (cps.map Char.ofNat)
          (Segmentation.sliceGraphemes s.toSlice).map String.Slice.copy == Segmentation.graphemes s &&
          (Segmentation.sliceBoundaries s.toSlice).map (fun p => p.offset.byteIdx) ==
            (Segmentation.boundaries s).map
              (fun n => (String.ofList (s.toList.take n)).utf8ByteSize) &&
          ((Segmentation.sliceGraphemes s.toSlice).getLast?.map String.Slice.copy ==
            some (String.ofList ((cps.drop (cps.length - 2)).map Char.ofNat))))))
    let errors ← ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).mapM (·.toString)
    modifyThe Core.State fun st => { st with messages := saved }
    unless errors.isEmpty do
      throwError "the ASCII path cut before a joining code point: {errors}"
  trivial
