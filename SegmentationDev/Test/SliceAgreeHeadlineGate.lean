import Lean
import Segmentation
import SegmentationDev.Gate.Axioms

-- "`sliceGraphemes_agree` is in both `SegmentationDev/Test/HeadlineAxioms.lean` and
-- `SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean`, and the axiom gate passes."
-- The gate command must leave no error for the theorem. The CI gate file must name it in its
-- `#assert_axioms` command; the printed-output test must name it in the quoted command and in its
-- `for` list. A mention in a docstring or comment does not count.
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
    -- Read only the code that names the theorems, not the docstrings or comments around it: the
    -- text from `opening` up to the next `closing` must name the theorem.
    let names : String → String → String → Bool := fun text opening closing =>
      match text.splitOn opening with
      | _ :: after :: _ => decide ((((after.splitOn closing).headD "").splitOn name).length > 1)
      | _ => false
    let gate ← IO.FS.readFile "SegmentationDev/Test/HeadlineAxioms.lean"
    unless names gate "\n#assert_axioms " "\n\n" do
      throwError "the #assert_axioms command in HeadlineAxioms.lean does not name {name}"
    let printed ← IO.FS.readFile "SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean"
    unless names printed "#assert_axioms " ")))" do
      throwError "the quoted #assert_axioms in AssertAxiomsPrintsHeadlineAxioms.lean omits {name}"
    unless names printed "for name in [" "] do" do
      throwError "the expected-name list in AssertAxiomsPrintsHeadlineAxioms.lean omits {name}"
  trivial
