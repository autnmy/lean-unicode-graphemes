import Lean
import Segmentation
import SegmentationDev.Gate.Axioms

-- "`sliceGraphemes_agree` is in both `SegmentationDev/Test/HeadlineAxioms.lean` and
-- `SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean`, and the axiom gate passes."
-- The gate command must leave no error for the theorem. The CI gate file names it once in its
-- list; the printed-output test names it twice, in the quoted command and in its `for` list.
open Lean Elab Command in
theorem sliceGraphemes_agree_passes_gate_and_is_in_both_headline_lists : True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    liftCommandElabM (elabCommand (← `(command|
      #assert_axioms Segmentation.sliceGraphemes_agree)))
    let failed := (← getThe Core.State).messages.hasErrors
    modifyThe Core.State fun s => { s with messages := saved }
    if failed then
      throwError "the gate rejects Segmentation.sliceGraphemes_agree"
    let name := "Segmentation.sliceGraphemes_agree"
    for (path, wanted) in [("SegmentationDev/Test/HeadlineAxioms.lean", 1),
        ("SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean", 2)] do
      let text ← IO.FS.readFile path
      let count := (text.splitOn name).length - 1
      unless count ≥ wanted do
        throwError "{path} names {name} {count} times, expected at least {wanted}"
  trivial
