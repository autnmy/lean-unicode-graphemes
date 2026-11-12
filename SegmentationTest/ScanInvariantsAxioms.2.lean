import Lean
import Segmentation

open Lean in
-- "For each lemma, run `collectAxioms` and throw on anything outside `[propext, Classical.choice, Quot.sound]`"
theorem «the scan invariant lemmas use only propext, Classical.choice and Quot.sound» : True := by
  run_tac do
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let lemmas := [``Segmentation.scanStateOf_prev, ``Segmentation.scanStateOf_linkerTail,
      ``Segmentation.scanStateOf_pictTail, ``Segmentation.scanStateOf_zwjAfterPict,
      ``Segmentation.scanStateOf_riOdd, ``Segmentation.breaksBefore_iff_isBoundary,
      ``Segmentation.isBoundary_zero, ``Segmentation.isBoundary_length]
    for name in lemmas do
      let used ← collectAxioms name
      for ax in used do
        unless allowed.contains ax do
          throwError "{name} depends on axiom {ax}"
  trivial
