import Segmentation

/-!
Checks `Range.lookup_eq_scan` in `Segmentation.RangeLookup` against kernel evaluation of both
sides on a small sorted table.
-/

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
