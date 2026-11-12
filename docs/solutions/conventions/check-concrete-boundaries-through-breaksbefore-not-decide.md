---
module: SegmentationTest
date: 2026-11-12
problem_type: convention
component: testing_framework
severity: low
audience: both
related_components:
  - Segmentation/ScanInvariants.lean
tags:
  - isboundary
  - decide
  - tests
  - decidable
applies_when:
  - Writing a test that a concrete text has, or has no, boundary at a position
---

# Check concrete boundaries through breaksBefore, not by deciding IsBoundary

## Context

Tests often need to say "this small text has no boundary at position 2". `IsBoundary` is the specification's definition of a boundary. It is built from `Rule.Applies`, which holds functions (patterns over lists). So `IsBoundary` has no `Decidable` instance, and `decide` cannot prove a concrete `IsBoundary` or its negation.

## Solution

Decide the scanner's verdict instead, then convert it with `breaksBefore_iff_isBoundary`. Position `i + 1` of `c :: cs` maps to index `i` of `cs`:

```lean
theorem «CR then LF has no boundary at position 1» :
    ¬ IsBoundary (fun c => if c = '\r' then crProps else lfProps) ['\r', '\n'] 1 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary (fun c => if c = '\r' then crProps else lfProps)
    '\r' ['\n'] 0 (by decide)).mpr h
  exact absurd hb (by decide)
```

For a positive boundary, use `.mp (by decide)`. Write `Props` values and the `Char → Props` lookup by hand, so `decide` never reads the generated tables. Positions 0 and `cs.length` are not covered by this lemma. Use `isBoundary_zero` and `isBoundary_length` for them.

## Why it matters

Trying `decide` on `IsBoundary` fails with a missing-instance error. That error does not point to the workaround. Going through the proved equivalence keeps the test about the specification and still lets the kernel compute the answer. It also avoids `native_decide`, which this repository forbids.

## Evidence

PR #21 adds `SegmentationTest/ScanInvariants.lean`. Its module doc comment says that `IsBoundary` holds functions, has no `Decidable` instance, and that boundary checks go through `breaksBefore_iff_isBoundary`. The CR LF, GB11, GB12, GB13 and GB999 cases in that file all use this shape. `breaksBefore_iff_isBoundary`, `isBoundary_zero` and `isBoundary_length` are defined in `Segmentation/ScanInvariants.lean`. `lake test` passes on this change.
