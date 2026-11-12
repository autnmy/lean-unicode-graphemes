import Lean
import Segmentation

/-!
Checks of `Range.Sorted` on arrays and of `Range.lookup_eq_scan` in `Segmentation.RangeLookup`.
-/

-- Each way a table can break the binary search's precondition is rejected on an array, beside a
-- gapped array that passes, so a check that always answers one way fails here.
open Segmentation.Tables in
theorem «Range.Sorted rejects out-of-order, overlapping and inverted arrays and accepts a gapped one» :
    ¬ Range.Sorted (#[⟨10, 12, 1⟩, ⟨1, 2, 2⟩] : Array (Range Nat)) ∧
      ¬ Range.Sorted (#[⟨1, 6, 1⟩, ⟨4, 9, 2⟩] : Array (Range Nat)) ∧
      ¬ Range.Sorted (#[⟨7, 3, 1⟩] : Array (Range Nat)) ∧
      Range.Sorted (#[⟨1, 2, 1⟩, ⟨5, 5, 2⟩, ⟨8, 20, 3⟩] : Array (Range Nat)) := by
  decide

-- The theorem's two sides, both evaluated by the kernel, agree with what applying it says at a
-- hit in each range, in each gap, and past the end.
open Segmentation.Tables in
theorem «lookup_eq_scan agrees with kernel evaluation on a small sorted table» :
    let table : Array (Range Nat) := #[⟨1, 2, 1⟩, ⟨5, 5, 2⟩, ⟨8, 20, 3⟩]
    (∀ n, Range.lookup 0 table n = Range.scan 0 table n) ∧
      (Range.lookup 0 table 1, Range.lookup 0 table 5, Range.lookup 0 table 20,
       Range.lookup 0 table 3, Range.lookup 0 table 21)
        = (Range.scan 0 table 1, Range.scan 0 table 5, Range.scan 0 table 20,
           Range.scan 0 table 3, Range.scan 0 table 21) := by
  intro table
  exact ⟨Range.lookup_eq_scan (by decide), by decide⟩

-- `#print axioms` only prints, so this reads the same axiom list and fails on anything beyond
-- `propext`, `Classical.choice` and `Quot.sound`. A proof by `sorry` depends on `sorryAx`.
open Lean in
theorem «Range.lookup_eq_scan uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.Tables.Range.lookup_eq_scan
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.Tables.Range.lookup_eq_scan depends on the disallowed axiom {ax}"
  trivial
