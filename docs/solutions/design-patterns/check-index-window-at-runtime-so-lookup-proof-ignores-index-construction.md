---
module: Segmentation
date: 2026-11-16
problem_type: design_pattern
component: property_lookup
severity: medium
audience: both
related_components:
  - Segmentation/Slice.lean
  - Segmentation/RangeLookup.lean
tags:
  - range-lookup
  - block-index
  - kernel-recursion-depth
  - proof-design
applies_when:
  - Speeding up a binary search over a sorted generated range table with a precomputed index
  - Proving a faster lookup equal to an existing lookup for every input
---
# Check an index window at run time so the lookup proof never reasons about the index

## Context

The scanner looks up the Unicode properties of each non-ASCII code point. That lookup is a binary search over the whole sorted table `Tables.propsRanges`. To make it faster, an index `propsBlockStarts` stores, for each block of 256 code points, where that block's ranges start in the table. The faster lookup must still be proved equal to `Tables.propsLookup` for every `Char`.

Proving the index itself correct means reasoning about the fold that builds it over the generated table. That proof is long, and the generated data can blow it up.

## Solution

Do not prove the index correct. Prove instead that any window that passes a cheap run-time check gives the right answer, and fall back to the whole table when the check fails.

1. Write a check on a window of the table, `Range.windowHolds table n start stop`. The window passes when `stop` is inside the table, the range just before `start` ends before `n`, and the range at `stop` starts after `n`. On a sorted table, no range outside such a window can hold `n`.
2. Prove once, over any sorted table, that searching a passing window equals the full lookup (`Range.lookup_search_window_eq_lookup`).
3. Have the function that picks the window (`propsBlockWindow`) return `none` when the check fails. The lookup searches the whole table on `none`.
4. Pass the window to the searching function as an argument (`searchPropsWindow c window`). Then prove equality for any window the check accepts, and apply it to `propsBlockWindow c.toNat`.

Step 4 matters. If the proof cases directly on `propsBlockWindow c.toNat`, the kernel must reduce that term, and the reduction exceeds its recursion depth. With the window as a variable, the proof matches on `some` or `none` and never reduces the index.

## Why it matters

The equality theorem `nonAsciiProps_eq_propsLookup` holds whatever `propsBlockStarts` contains. A later change to the index, the block size or the generated table cannot break the proof. At worst, such a change makes the lookup slower. The run-time check costs a few bounds checks and comparisons per lookup (the block bound in `propsBlockWindow`, and `stop ≤ size`, `table[before].hi < n` and `n < table[stop].lo` in `windowHolds`), which is less than the search it saves.

The cost of this design is that a wrong index fails without a sign: the output stays correct and only the speed is lost. A separate test must check that the fast path is taken (see the convention on testing fallback coverage through the production function).

## Evidence

- PR #101 adds `Range.windowHolds` and `Range.lookup_search_window_eq_lookup` to `Segmentation/RangeLookup.lean`. The theorem's hypotheses are only `Range.Sorted table` and `windowHolds ... = true`, and nothing about any index.
- PR #101 adds `propsBlockWindow`, `searchPropsWindow`, `searchPropsWindow_eq_propsLookup`, `nonAsciiProps` and `nonAsciiProps_eq_propsLookup` to `Segmentation/Slice.lean`. The `searchPropsWindow` docstring states that taking the window as an argument lets the proof case on it, because casing on `propsBlockWindow c.toNat` directly exceeds the kernel's recursion depth.
- The `nonAsciiProps` docstring in `Segmentation/Slice.lean` states that a code point with no window is looked up in the whole table, so the result never depends on how `propsBlockStarts` was built.
