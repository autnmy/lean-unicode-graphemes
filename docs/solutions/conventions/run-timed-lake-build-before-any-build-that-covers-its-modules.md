---
module: ci
date: 2026-11-15
problem_type: convention
component: development_workflow
severity: medium
audience: both
related_components:
  - lake
  - github-actions
tags:
  - ci
  - timeout
  - step-order
  - lake-build
applies_when:
  - A CI step uses timeout-minutes to bound how long a proof or module takes to compile
  - Steps in .github/workflows/ci.yml are added, removed or reordered
---

# Run a timed lake build before any build that covers its modules

## Context

CI checks the GraphemeBreakTest.txt theorem with a step that has `timeout-minutes: 10`. The limit exists so that a `decide +kernel` proof that grows to ten minutes or more fails CI. But Lake does not compile a module again when it is already up to date. The time limit therefore bounds only the modules that this step itself compiles.

The theorem modules sit in the `SegmentationChecks` library, whose glob is `SegmentationDev.Test.+`. Any step that builds that library compiles the theorem too.

## Solution

- Put the timed step before any build that includes the timed modules. In `.github/workflows/ci.yml` the order is: `lake build --wfail` (the Segmentation library only), then the timed step, then the build of `SegmentationTableGen SegmentationChecks ...`.
- When you add, remove or move a step before the timed one, check what it used to prebuild. Whatever it no longer builds is now compiled inside the time window.
- Keep the comment above the timed step accurate about what the limit covers. It should name the dependencies the step compiles, not only the proof.

## Why it matters

If a wider build runs first, the timed step reuses its result and finishes in seconds. CI stays green, and the check that guards against a slow proof checks nothing.

The reverse also happens. Before this change, the setup action ran `lake test` before the timed step, and that built `SegmentationDev.TableGen`, `GraphemeBreakTestFile` and `SegmentationDev.Gate.Axioms`. With the action's test run turned off, those compiles moved inside the 10-minute window. The limit got stricter, and a slow runner can now fail over compile time unrelated to the proof. Neither effect shows in the diff of the step that was moved.

## Evidence

- PR #74 changes `.github/workflows/ci.yml`: it adds the comment that the timed step "must compile its two modules itself, before the build of the development libraries", and puts the `SegmentationChecks` build after the timed step.
- The same file's comment on the timed step now says only the Segmentation library is built before it, so the limit also covers compiling `SegmentationDev.TableGen`, `SegmentationDev.Test.GraphemeBreakTestFile`, `SegmentationDev.Test.GraphemeBreakTestData` and `SegmentationDev.Gate.Axioms`.
- A review finding on PR #74 traced this through the imports: the theorem imports `Gate.Axioms`, `GraphemeBreakTestData` and `GraphemeBreakTestLine`; `GraphemeBreakTestData` imports `GraphemeBreakTestFile`, which imports `TableGen`.
