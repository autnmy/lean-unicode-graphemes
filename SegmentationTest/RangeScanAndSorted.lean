import Segmentation

/-!
Checks of `Segmentation.RangeLookup`: the reference scan `Range.scan`, the sortedness check
`Range.chainOK` behind `Range.Sorted`, and the statement of `Range.lookup_eq_scan`.
-/

-- The ascription pins the theorem to `Range.lookup` itself, as `Tables.props` calls it, for every
-- sorted table and every `n`, so a theorem about a copy of the search, one with an extra
-- hypothesis, or one bounded on `n` fails here.
theorem «lookup_eq_scan states that Range.lookup equals Range.scan on every sorted table for every n»
    {α : Type} {d : α} {table : Array (Segmentation.Tables.Range α)}
    (h : Segmentation.Tables.Range.Sorted table) (n : Nat) :
    Segmentation.Tables.Range.lookup d table n = Segmentation.Tables.Range.scan d table n :=
  Segmentation.Tables.Range.lookup_eq_scan h n

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

open Segmentation.Tables in
-- A range holds `lo` to `hi`, both included. A half-open reference would miss `hi`, and a
-- reference that ignored the default would not give it in gaps, past the end or on an empty
-- table.
theorem «Range.scan gives the value at both ends of a range and the default in a gap, past the end and on an empty table» :
    let table : Array (Range Nat) :=
      #[{ lo := 10, hi := 20, value := 1 }, { lo := 30, hi := 30, value := 2 }]
    (Range.scan 0 table 10, Range.scan 0 table 20, Range.scan 0 table 21,
     Range.scan 0 table 9, Range.scan 0 table 30, Range.scan 0 table 31,
     Range.scan 7 (#[] : Array (Range Nat)) 5)
      = (1, 1, 0, 0, 2, 0, 7) ∧
    (Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 2,
     Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 4,
     Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 5,
     Range.scan 0 (#[⟨2, 4, 7⟩] : Array (Range Nat)) 1,
     Range.scan 9 (#[] : Array (Range Nat)) 3)
      = (7, 7, 0, 0, 9) := by
  decide

-- On an unsorted, overlapping list the reference still has one answer: the first range in list
-- order that holds `n`, not the later one and not whatever a halving search would land on.
open Segmentation.Tables in
theorem «Range.scanList returns the first matching range in list order when ranges overlap» :
    let ranges : List (Range Nat) :=
      [{ lo := 0, hi := 9, value := 1 }, { lo := 5, hi := 15, value := 2 }]
    (Range.scanList 0 ranges 5, Range.scanList 0 ranges 12, Range.scanList 0 ranges 16,
     Range.scanList 4 ([] : List (Range Nat)) 0,
     Range.scanList 0 ([⟨1, 5, 10⟩, ⟨3, 8, 20⟩] : List (Range Nat)) 4,
     Range.scanList 0 ([⟨1, 5, 10⟩, ⟨3, 8, 20⟩] : List (Range Nat)) 7,
     Range.scan 0 (#[⟨1, 5, 10⟩, ⟨3, 8, 20⟩] : Array (Range Nat)) 4)
      = (1, 2, 0, 4, 10, 20, 10) := by
  decide

-- Each bad list is paired with valid ones, so a check that always answers false fails too.
-- Ranges that share an endpoint (`hi = next.lo`) overlap at that code point and must fail;
-- adjacent ranges (`next.lo = hi + 1`) share none and must pass, so a check stricter than
-- `hi < next.lo` would reject valid tables.
open Segmentation.Tables in
theorem «Range.chainOK rejects out-of-order, overlapping, endpoint-sharing and reversed ranges and accepts gapped and adjacent lists» :
    (Range.chainOK ([{ lo := 10, hi := 20, value := 1 }, { lo := 0, hi := 5, value := 2 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 10, value := 1 }, { lo := 10, hi := 20, value := 2 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 10, value := 1 }, { lo := 5, hi := 20, value := 2 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 5, hi := 3, value := 1 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 3, value := 1 }, { lo := 5, hi := 5, value := 2 },
                     { lo := 9, hi := 12, value := 1 }] : List (Range Nat)),
     Range.chainOK ([{ lo := 0, hi := 3, value := 1 }, { lo := 4, hi := 6, value := 2 }] : List (Range Nat)),
     Range.chainOK ([] : List (Range Nat)))
      = (false, false, false, false, true, true, true) ∧
    (Range.chainOK ([⟨10, 12, 0⟩, ⟨1, 2, 0⟩] : List (Range Nat)),
     Range.chainOK ([⟨1, 2, 0⟩, ⟨3, 3, 1⟩, ⟨7, 9, 2⟩] : List (Range Nat)),
     Range.chainOK ([⟨1, 5, 1⟩, ⟨5, 8, 2⟩] : List (Range Nat)))
      = (false, true, false) := by
  decide

open Segmentation.Tables in
-- Each consecutive pair has `hi < next.lo` (2 < 10 and 4 < 6), but the middle range has
-- `lo > hi`, so the first and last ranges are not ordered by that chain. Only the per-range
-- `lo ≤ hi` check catches it.
theorem «chainOK rejects an inverted range even when every neighbour pair is ordered» :
    Range.chainOK ([⟨1, 2, 0⟩, ⟨10, 4, 0⟩, ⟨6, 7, 0⟩] : List (Range Nat)) = false := by
  decide

open Segmentation.Tables in
theorem «Range.Sorted holds for a gapped array and fails for an array whose second range reaches back over the first» :
    Range.Sorted (#[{ lo := 0, hi := 3, value := 1 }, { lo := 7, hi := 9, value := 2 }] : Array (Range Nat)) ∧
      ¬ Range.Sorted (#[{ lo := 0, hi := 8, value := 1 }, { lo := 7, hi := 9, value := 2 }] : Array (Range Nat)) := by
  decide
