import Lean
import Segmentation.ScanInvariants

-- "For each lemma, run `collectAxioms` and throw on anything outside `[propext, Classical.choice, Quot.sound]`"
-- `#print axioms` only prints, so a sorry would not fail the check; throwing does.
open Lean in
theorem «scan invariants: every lemma uses only propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let lemmas := [``Segmentation.scanStateOf_prev, ``Segmentation.scanStateOf_linkerTail,
      ``Segmentation.scanStateOf_pictTail, ``Segmentation.scanStateOf_zwjAfterPict,
      ``Segmentation.scanStateOf_riOdd, ``Segmentation.breaksBefore_iff_isBoundary,
      ``Segmentation.isBoundary_zero, ``Segmentation.isBoundary_length]
    for lemma in lemmas do
      let used ← collectAxioms lemma
      for ax in used do
        unless allowed.contains ax do
          throwError m!"{lemma} depends on the axiom {ax}"
  trivial
