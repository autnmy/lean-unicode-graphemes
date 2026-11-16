import Lean
import Segmentation

-- "It may use no axiom beyond the ones the existing four statements use."
open Lean in
/-- The equality theorem rests on no axiom beyond propext, Classical.choice and Quot.sound, so
a proof by sorry or by compiled evaluation fails here. -/
theorem breaks_before_fast_equality_uses_only_allowed_axioms : True := by
  run_tac do
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    let used ← collectAxioms ``Segmentation.breaksBeforeFast_eq_breaksBefore
    for ax in used do
      unless allowed.contains ax do
        throwError m!"breaksBeforeFast_eq_breaksBefore uses the axiom {ax}"
  trivial
