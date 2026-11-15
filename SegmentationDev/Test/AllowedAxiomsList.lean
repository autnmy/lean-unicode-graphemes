import Lean
import SegmentationDev.Gate.Axioms

-- "A CI step that prints `#print axioms` for each headline theorem (L6, L8) and fails on any
-- axiom outside `propext`, `Classical.choice` and `Quot.sound`, and on any of `sorry`, `admit`,
-- `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in project code."
open Lean in
theorem «allowedAxioms is exactly propext, Classical.choice and Quot.sound» : True := by
  run_tac do
    let allowed := SegmentationDev.Gate.allowedAxioms
    unless allowed.length == 3 && allowed.contains ``propext &&
        allowed.contains ``Classical.choice && allowed.contains ``Quot.sound do
      throwError m!"SegmentationDev.Gate.allowedAxioms is {allowed}, not exactly propext, Classical.choice and Quot.sound"
  trivial
