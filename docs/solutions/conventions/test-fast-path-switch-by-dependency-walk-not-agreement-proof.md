---
module: SegmentationDev.Test
date: 2026-11-16
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - Segmentation.Slice
  - SegmentationDev.Test.ReferenceBreakDecisionUnchanged
tags:
  - lean
  - dependency-walk
  - getusedconstants
  - fast-path
  - test-design
applies_when:
  - A caller is switched to a fast definition that is proved equal to a reference.
  - A test walks definition bodies to check which constants a definition reaches.
---

# Test a fast-path switch with a dependency walk, and never seed the walk with the name you assert

## Context

`scanClusters` now calls `breaksBeforeFast` instead of `breaksBefore`. Because `breaksBeforeFast_eq_breaksBefore` proves the two equal, `scanClusters_agree` and every theorem built on it prove whichever one the scanner calls. A green build cannot show that the switch happened.

## Solution

Add a test that walks the caller's definition body. Start from the caller, and push the result of `getUsedConstants` for each `Segmentation` `.defnInfo` it meets. Fail if the walk reaches the reference. Fail if it never reaches the fast definition. Walking through the `Segmentation` names also finds a call that well-founded recursion moved into a generated helper.

When a walk asserts that some name is reached, that name must not be one of the walk's starting roots. A root is in the `seen` set before any body is read, so the assertion passes even if no definition reads it. To check that `breaksBefore` still reads `breakRows`, read the constants of `breaksBefore`'s own body. Do not look up `breakRows` in a walk that started from it.

## Why it matters

Without the walk, a forgotten call swap leaves every proof green, and the speed-up never runs. A walk seeded with the asserted name also passes when the claim is false. For example, a reference rewritten to stop reading the rule table would pass it, while the unused table stays in place.

## Evidence

- PR #93, `SegmentationDev/Test/BreaksBeforeFast.lean`: `scanClusters_reaches_breaksBeforeFast_not_breaksBefore` walks from `Segmentation.scanClusters`. It throws if it meets `Segmentation.breaksBefore`, or if `Segmentation.breaksBeforeFast` is not in `seen`. Its comment says the agreement proofs hold whichever decision the scanner calls.
- PR #93, `SegmentationDev/Test/ReferenceBreakDecisionUnchanged.lean`: the walk starts from `breaksBefore`, `breakRows` and `clustersOf`. The `breakRows` check reads `breaksBefore`'s own `info.value.getUsedConstants`. A comment says `seen` cannot show the dependency, because `breakRows` is a root.
- A round 3 review finding on this pull request flagged the seeded-root check. The author's probe printed `Segmentation.breaksBefore: true` and `Segmentation.breaksBeforeFast: false` for direct use of `breakRows`, so the revised check can fail.
