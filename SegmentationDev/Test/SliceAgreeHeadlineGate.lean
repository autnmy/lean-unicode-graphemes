import Lean
import Segmentation
import SegmentationDev.Gate.Axioms

-- "`sliceGraphemes_agree` is in both `SegmentationDev/Test/HeadlineAxioms.lean` and
-- `SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean`, and the axiom gate passes."
-- "The four new theorems are in both axiom-gate name lists and the gate passes with only
-- `propext`, `Classical.choice`, `Quot.sound`."
-- The gate command must leave no error for any of the five theorems. The CI gate file must name
-- each in its `#assert_axioms` command; the printed-output test must name each in the quoted
-- command and in its `for` list. A mention in a docstring or comment does not count.
open Lean Elab Command in
theorem sliceGraphemes_agree_passes_gate_and_is_in_both_headline_lists : True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    liftCommandElabM (elabCommand (← `(command|
      #assert_axioms Segmentation.sliceGraphemes_agree Segmentation.graphemesFast_join
        Segmentation.graphemesFast_ne_empty Segmentation.graphemesFast_rules
        Segmentation.boundariesFast_agree)))
    let failed := (← getThe Core.State).messages.hasErrors
    modifyThe Core.State fun s => { s with messages := saved }
    if failed then
      throwError "the gate rejects one of the slice scanner's headline theorems"
    -- Read only the code that names the theorems, not the docstrings or comments around it: the
    -- text from `opening` up to the next `closing` must name the theorem.
    let names : String → String → String → String → Bool := fun text opening closing name =>
      match text.splitOn opening with
      | _ :: after :: _ => decide ((((after.splitOn closing).headD "").splitOn name).length > 1)
      | _ => false
    let gate ← IO.FS.readFile "SegmentationDev/Test/HeadlineAxioms.lean"
    let printed ← IO.FS.readFile "SegmentationDev/Test/AssertAxiomsPrintsHeadlineAxioms.lean"
    for name in ["Segmentation.sliceGraphemes_agree", "Segmentation.graphemesFast_join",
        "Segmentation.graphemesFast_ne_empty", "Segmentation.graphemesFast_rules",
        "Segmentation.boundariesFast_agree"] do
      unless names gate "\n#assert_axioms " "\n\n" name do
        throwError "the #assert_axioms command in HeadlineAxioms.lean does not name {name}"
      unless names printed "#assert_axioms " ")))" name do
        throwError "the quoted #assert_axioms in AssertAxiomsPrintsHeadlineAxioms.lean omits {name}"
      unless names printed "for name in [" "] do" name do
        throwError "the expected-name list in AssertAxiomsPrintsHeadlineAxioms.lean omits {name}"
  trivial
