---
module: Segmentation.RangeLookup
date: 2026-11-12
problem_type: design_pattern
component: tables
severity: medium
audience: both
related_components:
  - Segmentation.TableLookup
  - SegmentationDev.Test
tags:
  - range-table
  - binary-search
  - sortedness
  - lean-proof
applies_when:
  - Writing a check that a table of lo..hi ranges is sorted and non-overlapping
  - Proving a binary search over ranges correct from such a check
---

# A range sortedness check must test lo ≤ hi on every range, not only neighbour order

## Context

`Range.lookup` finds a code point's range by binary search. That is only correct when the table is sorted by `lo` and no two ranges overlap. The proof needs a fact about every pair of ranges in order: range `i` ends before range `j` starts whenever `i < j`. The tempting check tests only neighbours: `range.hi < next.lo` for each consecutive pair.

That check is not enough. Take `[⟨1, 2⟩, ⟨10, 4⟩, ⟨6, 7⟩]`. Each neighbour pair passes (2 < 10 and 4 < 6). But the middle range is inverted (`lo = 10 > hi = 4`), so the first and last ranges are not ordered by the chain, and a search can skip the range that holds a code point.

## Solution

Check both rules in one pass, as `Range.chainOK` does:

```lean
def Range.chainOK {α : Type} : List (Range α) → Bool
  | [] => true
  | [range] => decide (range.lo ≤ range.hi)
  | range :: next :: rest =>
    decide (range.lo ≤ range.hi) && decide (range.hi < next.lo) && chainOK (next :: rest)
```

With `lo ≤ hi` on each range, `hi_i < lo_(i+1) ≤ hi_(i+1) < lo_(i+2)` chains, so `hi < lo` holds for every ordered pair, not only neighbours. The lemma `Range.chainOK_hi_lt_lo` proves exactly this, and it uses `Range.chainOK_lo_le_hi` for the step across the middle range.

Use strict `<` between neighbours. Ranges that share an endpoint (`hi = next.lo`) both hold that code point and must fail. Adjacent ranges (`next.lo = hi + 1`) share none and must pass, so a stricter rule would reject valid tables.

## Why it matters

A check that misses the inverted-range case still passes every test built from ordinary gapped or overlapping lists. The proof then fails to go through, or worse, a hand-written argument trusts a check that lets a broken table through. Keep a test for the inverted middle range on its own, because only the per-range rule catches it.

## Evidence

- PR #18 adds `Range.chainOK`, `Range.Sorted`, `Range.chainOK_lo_le_hi` and `Range.chainOK_hi_lt_lo` in `Segmentation/RangeLookup.lean`. The docstring of `Range.chainOK` states that a middle range with `lo > hi` could otherwise sit between two ranges that overlap each other.
- `SegmentationDev/Test/RangeScanAndSorted.lean` in PR #18 has the test «chainOK rejects an inverted range even when every neighbour pair is ordered», which decides `Range.chainOK [⟨1, 2, 0⟩, ⟨10, 4, 0⟩, ⟨6, 7, 0⟩] = false`.
- The same file's chainOK test rejects the endpoint-sharing list `[⟨1, 5, 1⟩, ⟨5, 8, 2⟩]` and accepts the adjacent list `{lo := 0, hi := 3}, {lo := 4, hi := 6}`.
