import Lean
import Segmentation

-- "The theorem is proved with no `sorry`, and `#print axioms` shows nothing beyond the three
-- standard axioms." `#print axioms` only prints, so this reads the same list and fails on
-- anything else, including axioms reached through the per-table sortedness proofs.
open Lean in
theorem «props_eq_scan uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.Tables.props_eq_scan
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.Tables.props_eq_scan depends on the disallowed axiom {ax}"
  trivial
