import Segmentation

open Segmentation.Tables in
-- Out-of-order ranges must fail. Ranges where `next.lo = hi + 1` hold no shared code point,
-- so they must pass; a check stricter than `hi < next.lo` would reject valid tables.
theorem «chainOK rejects out-of-order ranges and accepts ranges that touch without overlap» :
    (Range.chainOK ([⟨10, 12, 0⟩, ⟨1, 2, 0⟩] : List (Range Nat)) = false ∧
     Range.chainOK ([⟨1, 2, 0⟩, ⟨3, 3, 1⟩, ⟨7, 9, 2⟩] : List (Range Nat)) = true ∧
     Range.chainOK ([] : List (Range Nat)) = true) := by
  decide
