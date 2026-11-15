import Lean
-- The script elaborates throwaway files that import `SegmentationDev.Gate.Axioms`; importing it
-- here makes Lake build the current gate before this check runs.
import SegmentationDev.Gate.Axioms

-- The issue asks for a step that "fails on any axiom outside `propext`, `Classical.choice` and
-- `Quot.sound`". A gate that only passes on a clean tree proves nothing, so the self-test script
-- plants each forbidden axiom in a throwaway file and exits 0 only when the gate rejects all of them.
open Lean in
theorem axiom_gate_self_test_rejects_sorry_native_decide_and_user_axiom :
    True := by
  run_tac do
    let out ← IO.Process.output { cmd := "sh", args := #["scripts/axiom-gate-self-test.sh"] }
    unless out.exitCode == 0 do
      throwError m!"scripts/axiom-gate-self-test.sh exited {out.exitCode}:\n{out.stdout}\n{out.stderr}"
  trivial
