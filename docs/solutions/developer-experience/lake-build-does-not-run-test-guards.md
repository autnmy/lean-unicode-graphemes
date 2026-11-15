---
module: SegmentationDev.Test
date: 2026-11-12
problem_type: developer_experience
component: development_workflow
severity: medium
audience: both
related_components:
  - SegmentationDev/Test.lean
  - lake test
tags:
  - lake
  - guard
  - acceptance-criteria
  - default-targets
applies_when:
  - An issue says "`lake build` is green" and also asks for `#guard` checks
  - Adding new test modules under SegmentationDev/Test/
---

# `lake build` does not run the `#guard` checks; `lake test` does

## Context

In this repository, plain `lake build` builds only the default target, the `Segmentation` library. The `#guard` checks live in `SegmentationDev/Test/` modules, and the test driver `SegmentationDev/Test.lean` imports them. Only `lake test` runs that driver. Issues still word their acceptance criteria as "`lake build` is green, and the functions agree … as `#guard` checks".

## Solution

- Put new guard files under `SegmentationDev/Test/` and import each one from `SegmentationDev/Test.lean`. If a file is not imported, `lake test` never runs it.
- Read "`lake build` is green" as two checks: `lake build` for the library and `lake test` for the guards. CI runs both.
- Don't move test code into the library or widen the default targets just to meet the literal wording. That changes what every user builds. Instead, state the difference in the pull request.

## Why it matters

A reviewer who sees only a green `lake build` has no evidence that any guard passed. A guard file left out of `SegmentationDev/Test.lean` never runs, so it can be wrong without anyone noticing.

## Evidence

- The PR #14 body records the deviation. `lake build` is green, but the guards run under `lake test` because the default `lake build` target builds only the library. The same body reports `lake test` exiting 0 with "10 checks passed".
- PR #14 adds seventeen `import SegmentationTest.Graphemes…` and `import SegmentationTest.BoundariesAgreesWithCore` lines to `SegmentationTest.lean` (now `SegmentationDev/Test.lean`) so that `lake test` runs the new guards.
- The `README.md` status text in PR #14 says the functions are checked against `GraphemeBreakTest.txt` lines in `lake test`.
