import Segmentation

-- Overlap (0..10 with 5..15), a gap no range covers (16..19), and ranges that touch across the
-- two lists (20..25 then 26..30). Each probe sits on or next to a boundary, where a split written
-- as `hi` instead of `lo - 1` would give the wrong pair for exactly one code point.
open Segmentation.Tables in
theorem «mergeWith_splits_overlapping_touching_and_gap_ranges» :
    let a : List (Range Nat) :=
      [{ lo := 0, hi := 10, value := 1 }, { lo := 20, hi := 25, value := 2 }]
    let b : List (Range Bool) :=
      [{ lo := 5, hi := 15, value := true }, { lo := 26, hi := 30, value := true }]
    let merged := Range.mergeWith Prod.mk 0 false a b
    Range.chainOK merged = true ∧
    ([0, 4, 5, 10, 11, 15, 16, 19, 20, 25, 26, 30, 31].map (Range.scanList (0, false) merged)) =
      [(1, false), (1, false), (1, true), (1, true), (0, true), (0, true), (0, false),
       (0, false), (2, false), (2, false), (0, true), (0, true), (0, false)] := by
  decide
