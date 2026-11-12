import Lean
import Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, ..."
open Lean in
theorem «disallowedAxioms reports sorryAx, Lean.ofReduceBool and a made-up axiom but none of propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used := #[``propext, ``sorryAx, ``Classical.choice, `Lean.ofReduceBool, ``Quot.sound,
      `Gate.madeUpAxiomForTest]
    let got := Gate.disallowedAxioms used
    let expected := [``sorryAx, `Lean.ofReduceBool, `Gate.madeUpAxiomForTest]
    unless got.length == expected.length && expected.all got.contains do
      throwError m!"disallowedAxioms {used} gave {got}, expected {expected}"
    let clean := Gate.disallowedAxioms #[``propext, ``Classical.choice, ``Quot.sound]
    unless clean.isEmpty do
      throwError m!"the three allowed axioms were reported as disallowed: {clean}"
    unless (Gate.disallowedAxioms #[]).isEmpty do
      throwError m!"an empty axiom list reported a disallowed axiom"
  trivial
