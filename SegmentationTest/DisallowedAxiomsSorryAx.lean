import Lean
import Gate.Axioms

-- A proof by the forbidden placeholder tactic depends on `sorryAx`, which is outside
-- `propext`, `Classical.choice` and `Quot.sound`, so the gate must report it.
open Lean in
theorem «disallowedAxioms reports sorryAx and keeps propext out» : True := by
  run_tac do
    let got := Gate.disallowedAxioms #[``propext, ``sorryAx]
    unless got == [``sorryAx] do
      throwError m!"expected [sorryAx], got {got}"
  trivial
