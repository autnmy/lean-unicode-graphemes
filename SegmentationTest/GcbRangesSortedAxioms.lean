import Lean
import Segmentation

-- A proof by `native_decide` depends on `Lean.ofReduceBool`, and a proof by `sorry` on
-- `sorryAx`; neither is in the allowed list, so either fails here.
open Lean in
theorem «gcbRanges_sorted is kernel-checked with no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.Tables.gcbRanges_sorted
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.Tables.gcbRanges_sorted depends on the disallowed axiom {ax}"
  trivial
