---
module: Segmentation
date: 2026-11-16
problem_type: convention
component: property_lookup
severity: medium
audience: both
related_components:
  - Segmentation/Slice.lean
  - SegmentationDev/Test/SliceFastLookup.lean
tags:
  - fast-path
  - silent-fallback
  - test-design
  - single-source-of-truth
applies_when:
  - A fast path is proved equal to a slow path and falls back to the slow path without error
  - A test checks that the fast path is taken for every input class
---
# Test fast-path coverage through the production selector, not a copy of its rule

## Context

The scanner's `nonAsciiProps` searches a small window of `Tables.propsRanges` when `propsBlockWindow` gives one. When it gives `none`, the scanner searches the whole table. The theorem `nonAsciiProps_eq_propsLookup` holds in both cases. So if the window rule breaks, the output stays correct and every non-ASCII lookup becomes slow again, and no proof or agreement check reports it.

The only check that catches this fallback is a test that every block of the index gets a window. An earlier version of that test worked out each window with its own copy of the formula in `nonAsciiProps`.

## Solution

Put the rule that picks the fast path in one named function, and have the test call that function.

- `propsBlockWindow n` returns `some (start, stop)` only when the block is inside the index and the window passes `Tables.Range.windowHolds`. `nonAsciiProps` reads it.
- The test asserts `(Segmentation.propsBlockWindow n).isSome` at the first and last code point of every block, and at the end of the last range.
- `propsBlockWindow` joins the list of definitions that must be plain and the `#assert_axioms` list, like the rest of the scanner.

## Why it matters

A copied rule tests the copy. If someone later edits the production window, the guards keep passing against the old rule while the scanner falls back on every non-ASCII code point. Correctness tests cannot catch this, because the fallback is correct by design. Only a test that calls the production selector ties the speed guarantee to the code that runs.

The same rule applies to any proved fast path that degrades silently: the coverage test must call the same function the fast path calls.

## Evidence

- In PR #101, `Segmentation/Slice.lean` defines `propsBlockWindow`, and `nonAsciiProps` is `searchPropsWindow c (propsBlockWindow c.toNat)`, which searches the whole table on `none`.
- `SegmentationDev/Test/SliceFastLookup.lean` in PR #101 guards `(Segmentation.propsBlockWindow (block * Segmentation.propsBlockSize)).isSome` and the same at each block's last code point. A comment there says this keeps the scanner from quietly falling back to the whole-table search.
- `SegmentationDev/Test/SliceAgrees.lean` in PR #101 adds `Segmentation.propsBlockWindow` to the plain-definition list.
- A review of PR #101 found that the test helper had copied the window formula from `nonAsciiProps`. The fix moved the rule into `propsBlockWindow`, and the guards now call it.
