import Lean

-- The issue asks for a step that "fails on any axiom outside `propext`, `Classical.choice` and
-- `Quot.sound`". A gate that only passes on a clean tree proves nothing, so the self-test script
-- plants each forbidden axiom in a throwaway file and exits 0 only when the gate rejects all of them.
open Lean in
theorem «axiom gate self-test script confirms the gate fails on sorryAx, Lean.ofReduceBool and a user axiom» :
    True := by
  run_tac do
    let out ← IO.Process.output { cmd := "sh", args := #["scripts/axiom-gate-self-test.sh"] }
    unless out.exitCode == 0 do
      throwError m!"scripts/axiom-gate-self-test.sh exited {out.exitCode}:\n{out.stdout}\n{out.stderr}"
  trivial
