import Lean
import Segmentation

-- "The theorem is proved with no `sorry`, and `#print axioms` shows nothing beyond the three
-- standard axioms." `#print axioms` only prints, so this reads the same axiom list and fails on
-- anything else; a proof by `sorry` depends on `sorryAx`.
open Lean in
theorem «lookup_eq_scan and the table corollaries use no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let names := [``Segmentation.Tables.Range.lookup_eq_scan,
      ``Segmentation.Tables.gcbRanges_sorted, ``Segmentation.Tables.extPictRanges_sorted,
      ``Segmentation.Tables.incbRanges_sorted, ``Segmentation.Tables.gcbOf_eq_scan,
      ``Segmentation.Tables.extPictOf_eq_scan, ``Segmentation.Tables.incbOf_eq_scan,
      ``Segmentation.Tables.props_eq_scan]
    for name in names do
      let used ← collectAxioms name
      for ax in used do
        unless allowed.contains ax do
          throwError m!"{name} depends on the disallowed axiom {ax}"
  trivial
