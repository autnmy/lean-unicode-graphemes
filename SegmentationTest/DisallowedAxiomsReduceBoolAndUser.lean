import Lean
import Gate.Axioms

-- Kernel evaluation through the compiler shows up as `Lean.ofReduceBool`, and a user `axiom`
-- shows up under its own name; both are outside the three allowed axioms.
open Lean in
theorem «disallowedAxioms reports Lean.ofReduceBool and a user-declared axiom» : True := by
  run_tac do
    let user : Name := `Gate.madeUpAxiomForThisTest
    let got := Gate.disallowedAxioms #[``Classical.choice, `Lean.ofReduceBool, ``Quot.sound, user]
    unless got.length == 2 && got.contains `Lean.ofReduceBool && got.contains user do
      throwError m!"expected Lean.ofReduceBool and {user}, got {got}"
  trivial
