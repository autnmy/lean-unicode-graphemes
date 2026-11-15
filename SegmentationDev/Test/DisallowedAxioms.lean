import Lean
import SegmentationDev.Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, ..."
-- A proof by `sorry` depends on `sorryAx`. `Lean.ofReduceBool` stands for any other axiom
-- outside the allowed three, and a user `axiom` shows up under its own name.
-- Allowed axioms in the same list must not mask the others, and must not be reported
-- themselves. The rule is a subset check: a proof that uses all, some or none of the allowed
-- axioms passes. The result keeps the order of the input, so each expected list is exact.
open Lean in
theorem disallowedAxioms_reports_exactly_axioms_outside_allowed :
    True := by
  run_tac do
    let cases : List (Array Name × List Name) := [
      (#[``propext, ``sorryAx, ``Classical.choice, `Lean.ofReduceBool, ``Quot.sound],
        [``sorryAx, `Lean.ofReduceBool]),
      (#[``propext, ``sorryAx], [``sorryAx]),
      (#[``Classical.choice, `Lean.ofReduceBool, ``Quot.sound, `Gate.madeUpAxiomForThisTest],
        [`Lean.ofReduceBool, `Gate.madeUpAxiomForThisTest]),
      (#[``propext, ``sorryAx, ``Classical.choice, `Lean.ofReduceBool, ``Quot.sound,
          `Gate.madeUpAxiomForTest],
        [``sorryAx, `Lean.ofReduceBool, `Gate.madeUpAxiomForTest]),
      (#[``propext, ``Classical.choice, ``Quot.sound], []),
      (#[``propext], []),
      (#[], [])]
    for (used, expected) in cases do
      let got := SegmentationDev.Gate.disallowedAxioms used
      unless got == expected do
        throwError m!"disallowedAxioms {used} gave {got}, expected {expected}"
  trivial
