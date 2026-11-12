import Lean
import Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, ..."
open Lean in
theorem «allowedAxioms is exactly propext, Classical.choice and Quot.sound» : True := by
  run_tac do
    let expected := [``propext, ``Classical.choice, ``Quot.sound]
    let got := Gate.allowedAxioms
    unless got.length == expected.length && expected.all got.contains do
      throwError m!"allowedAxioms is {got}, expected {expected}"
  trivial
