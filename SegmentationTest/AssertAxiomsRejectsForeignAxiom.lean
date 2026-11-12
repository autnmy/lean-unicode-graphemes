import Lean
import Segmentation
import Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, ..."
-- The foreign axiom is added to the environment only while this proof runs, through `addDecl`,
-- so no axiom declaration appears in project code. The command must reject a theorem that
-- uses it, and must still accept a theorem that uses only the allowed axioms.
open Lean Elab Command in
theorem «assert_axioms fails on a theorem that rests on an axiom outside propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    -- Declarations added inside a proof must sit under the name of the theorem being proved.
    let pre := (← Term.getDeclName?).getD .anonymous
    let badAx := pre ++ `GateAcceptance.foreignAxiom
    let usesBad := pre ++ `GateAcceptance.usesForeignAxiom
    addDecl (.axiomDecl { name := badAx, levelParams := [], type := mkConst ``False, isUnsafe := false })
    addDecl (.thmDecl { name := usesBad, levelParams := [], type := mkConst ``False,
                        value := mkConst badAx })
    let saved := (← getThe Core.State).messages
    let rejected ← try
        liftCommandElabM (elabCommand (← `(command| #assert_axioms $(mkIdent usesBad))))
        pure false
      catch _ => pure true
    modifyThe Core.State fun s => { s with messages := saved }
    unless rejected do
      throwError "#assert_axioms accepted a theorem that depends on {badAx}"
    liftCommandElabM (elabCommand (← `(command| #assert_axioms Segmentation.isBoundary_zero)))
    modifyThe Core.State fun s => { s with messages := saved }
  trivial
