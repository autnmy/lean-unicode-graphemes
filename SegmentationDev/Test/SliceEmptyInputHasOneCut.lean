import Lean
import Segmentation

-- "The cuts include both ends, as `boundaries` does."
-- A scan that emits a cut only after each cluster returns no cut at all for the empty input; the
-- reference gives `[0]`.
open Lean Elab Command in
theorem «empty slice gives no clusters and a single cut at byte 0» : True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    modifyThe Core.State fun st => { st with messages := {} }
    liftCommandElabM (elabCommand (← `(command|
      #guard
        (Segmentation.sliceGraphemes "".toSlice).isEmpty &&
        (Segmentation.sliceBoundaries "".toSlice).map (fun p => p.offset.byteIdx) == [0] &&
        Segmentation.boundaries "" == [0])))
    let errors ← ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).mapM (·.toString)
    modifyThe Core.State fun st => { st with messages := saved }
    unless errors.isEmpty do
      throwError "the empty slice does not give one cut at byte 0: {errors}"
  trivial
