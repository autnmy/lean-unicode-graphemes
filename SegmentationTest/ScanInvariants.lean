import Lean
import Segmentation

/-!
Checks of the scan state invariants in `Segmentation.ScanInvariants`. The type ascriptions and
the small hand-built instances live in the `SegmentationTest.ScanInvariants*` files beside this
one; this file checks that each lemma is proved from the standard axioms only.
-/

-- `#print axioms` only prints, so a lemma that rests on `sorry` would still pass; throwing an
-- error from `collectAxioms` makes the build, and so `lake test`, fail instead. Each lemma has its
-- own check so a failure names the lemma.
open Lean in
theorem «scanStateOf_prev uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.scanStateOf_prev
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.scanStateOf_prev depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «scanStateOf_linkerTail uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.scanStateOf_linkerTail
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.scanStateOf_linkerTail depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «scanStateOf_pictTail uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.scanStateOf_pictTail
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.scanStateOf_pictTail depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «scanStateOf_zwjAfterPict uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.scanStateOf_zwjAfterPict
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.scanStateOf_zwjAfterPict depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «scanStateOf_riOdd uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.scanStateOf_riOdd
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.scanStateOf_riOdd depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «breaksBefore_iff_isBoundary uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.breaksBefore_iff_isBoundary
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.breaksBefore_iff_isBoundary depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «isBoundary_zero uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.isBoundary_zero
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.isBoundary_zero depends on the disallowed axiom {ax}"
  trivial

open Lean in
theorem «isBoundary_length uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.isBoundary_length
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.isBoundary_length depends on the disallowed axiom {ax}"
  trivial
