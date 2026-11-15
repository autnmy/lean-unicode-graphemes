import Lean
import Segmentation
import SegmentationDev.Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, ..."
-- L6 is JoinRestoresInput and ClustersNonEmpty (graphemes_join, graphemes_ne_empty) and L8 is
-- CutsMatchRules and BoundariesMatchCuts (graphemes_rules, boundaries_agree). The command must
-- pass on all four and leave one `#print axioms` message per theorem, naming it.
open Lean Elab Command in
theorem «assert_axioms prints the print axioms output for each of the four headline theorems» :
    True := by
  run_tac do
    let saved := (← getThe Core.State).messages
    liftCommandElabM (elabCommand (← `(command|
      #assert_axioms Segmentation.graphemes_join Segmentation.graphemes_ne_empty
        Segmentation.graphemes_rules Segmentation.boundaries_agree)))
    let msgs ← (← getThe Core.State).messages.toList.mapM (·.toString)
    modifyThe Core.State fun s => { s with messages := saved }
    for name in ["Segmentation.graphemes_join", "Segmentation.graphemes_ne_empty",
        "Segmentation.graphemes_rules", "Segmentation.boundaries_agree"] do
      let printed := msgs.filter fun m =>
        (m.splitOn s!"'{name}'").length > 1 && (m.splitOn "depends on axioms").length > 1
      unless printed.length == 1 do
        throwError "expected exactly one #print axioms message for {name}, got {printed.length}"
  trivial
