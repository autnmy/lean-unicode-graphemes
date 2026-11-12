import Lean
import Segmentation

-- "Both theorems are proved with no `sorry`, and `#print axioms` on each shows nothing beyond
-- `propext`, `Classical.choice` and `Quot.sound`."
-- `#print axioms` only prints, so this reads the same axiom list and fails on anything else.
-- A proof by `sorry` depends on `sorryAx`, which is not in the allowed list.
open Lean in
theorem «graphemes_ne_empty uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.graphemes_ne_empty
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.graphemes_ne_empty depends on the disallowed axiom {ax}"
  trivial
