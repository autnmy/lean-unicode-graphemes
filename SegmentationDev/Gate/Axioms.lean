import Lean

/-!
# The axiom rule

Every proved theorem in this library may depend only on `propext`, `Classical.choice` and
`Quot.sound`. `#print axioms` shows what a theorem depends on but never fails, so on its own it
checks nothing. `#assert_axioms` prints the same output and then fails elaboration when the
theorem depends on anything else. A proof that uses the placeholder tactic depends on `sorryAx`,
and one that evaluates through the compiler depends on an axiom that tactic adds (named like
`t._native.native_decide.ax_1_1` on this toolchain), so both fail here.
-/

namespace SegmentationDev.Gate

open Lean Elab Command

/-- The only axioms a proved theorem may depend on. This is the one copy of the list. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms in `used` that are not in `allowedAxioms`, in the order given. The rule is a subset
check, so a proof that stops using one of the allowed axioms still passes. -/
def disallowedAxioms (used : Array Name) : List Name :=
  used.toList.filter (!allowedAxioms.contains ·)

/-- `#assert_axioms n₁ n₂ …` runs `#print axioms` on each named declaration and fails if any of
them depends on an axiom outside `allowedAxioms`. A name that does not resolve fails too, so a
renamed theorem cannot drop out of the check unnoticed. -/
syntax (name := assertAxioms) "#assert_axioms" (ppSpace ident)+ : command

@[command_elab assertAxioms]
def elabAssertAxioms : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    elabCommand (← `(command| #print axioms $(mkIdent name)))
    let disallowed := disallowedAxioms (← collectAxioms name)
    unless disallowed.isEmpty do
      throwErrorAt id m!"{name} depends on the disallowed axioms {disallowed}"

end SegmentationDev.Gate
