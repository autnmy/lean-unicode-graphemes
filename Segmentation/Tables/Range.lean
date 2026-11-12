/-!
# Range tables

A property table is an array of code point ranges, each carrying one property
value. The arrays are sorted by `lo` and their ranges do not overlap, so a
lookup is a binary search. A code point that no range covers takes the
property's default value.

The range list and the lookup are kept as plain definitions, so proofs can
reason about them directly and `decide` can evaluate them in the kernel.
-/

namespace Segmentation.Tables

/-- The code points `lo` to `hi`, both included, all carrying `value`. -/
structure Range (α : Type) where
  lo : Nat
  hi : Nat
  value : α
  deriving Repr

/--
The value of the range in `table` that holds code point `n`, or `default` when
no range holds it. `table` must be sorted by `lo` with no overlapping ranges.
-/
def Range.lookup {α : Type} (default : α) (table : Array (Range α)) (n : Nat) : α :=
  -- Each step at least halves the search window, so `table.size + 1` steps are
  -- always enough; counting steps keeps the recursion structural, which the
  -- kernel can evaluate.
  search (table.size + 1) 0 table.size
where
  /-- Binary search over the indices `start` (included) to `stop` (excluded). -/
  search : Nat → Nat → Nat → α
    | 0, _, _ => default
    | steps + 1, start, stop =>
      if start < stop then
        let mid := (start + stop) / 2
        match table[mid]? with
        | none => default
        | some range =>
          if n < range.lo then search steps start mid
          else if range.hi < n then search steps (mid + 1) stop
          else range.value
      else default

end Segmentation.Tables
