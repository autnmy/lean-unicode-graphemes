import Lean
import Gate.Axioms

-- The rule is a subset check: a proof that uses all, some or none of the allowed axioms passes.
open Lean in
theorem «disallowedAxioms is empty for the three allowed axioms and for none» : True := by
  run_tac do
    let all := Gate.disallowedAxioms #[``propext, ``Classical.choice, ``Quot.sound]
    let some := Gate.disallowedAxioms #[``propext]
    let none := Gate.disallowedAxioms #[]
    unless all.isEmpty && some.isEmpty && none.isEmpty do
      throwError m!"expected no disallowed axioms, got {all}, {some}, {none}"
  trivial
