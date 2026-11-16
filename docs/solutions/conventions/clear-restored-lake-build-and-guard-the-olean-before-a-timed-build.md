---
module: ci
date: 2026-11-16
problem_type: convention
component: development_workflow
severity: medium
audience: both
related_components:
  - lean-action
  - lake
tags:
  - ci
  - lake-cache
  - timed-build
  - timeout-minutes
  - olean
applies_when:
  - A CI step uses `timeout-minutes` to bound how long a Lake build of a proof may take
  - A setup action may restore `.lake` from an earlier run's cache
---

# Clear restored `.lake/build` and guard the `.olean` before a timed Lake build

## Context

CI checks that the GraphemeBreakTest.txt theorem compiles within 10 minutes. It does this with a step that has `timeout-minutes: 10` and runs `lake build --wfail` on the theorem modules. The limit only means something if the proof is actually compiled inside that step.

Lake does not compile a module again when its output is up to date. The setup action (lean-action) can restore `.lake` from an earlier run's cache. If that cache holds the theorem's outputs, the timed step reuses an old proof, finishes in seconds, and passes. The check is green but has timed nothing.

The existing rule about running the timed build before any other build that covers its modules handles builds inside one run. It does not handle outputs that arrive from earlier runs through a cache.

## Solution

Do two things in `.github/workflows/ci.yml`:

1. Right after the setup action and before the first build, delete every build output:

   ```yaml
   - name: Remove build outputs restored from earlier runs
     run: rm -rf .lake/build
   ```

   Prefer this to turning the action's cache input off. Deleting the directory does not depend on the action's cache settings, on any cache key, or on which old caches the host still holds. A mistyped input name, by contrast, would not fail the job and would leave the cache on.

2. Make the first command of the timed step a guard on the theorem's output file, inside the same `run` block so nothing can run between check and build:

   ```sh
   set -eu
   prebuilt=.lake/build/lib/lean/SegmentationDev/Test/GraphemeBreakTestTheorem.olean
   if [ -e "$prebuilt" ]; then
     echo "$prebuilt exists before the timed build, so the 10-minute limit would not time the proof." >&2
     exit 1
   fi
   lake build --wfail SegmentationDev.Test.GraphemeBreakTestTheorem SegmentationDev.Test.GraphemeBreakTestTheoremTests
   ```

The guard catches both causes of a prebuilt proof: a cache, and a later edit that moves a covering build ahead of the timed step. Confirm the guard path is the path Lake really writes, by building the module locally and checking that the guard then exits 1. A guard on a wrong path passes while checking nothing.

The cost: every run now compiles cold. The modules the theorem imports outside the Segmentation library (such as `SegmentationDev.TableGen` and `SegmentationDev.Gate.Axioms`) compile inside the 10-minute window, so total job time grows.

## Why it matters

A time limit that passes on a cache hit gives false confidence: a proof that had become too slow would still show green. Deleting restored outputs fixes the cause. The guard is a backstop that turns any future reuse into a loud failure instead of a silent pass.

## Evidence

- PR #82 adds the step `Remove build outputs restored from earlier runs` running `rm -rf .lake/build` right after lean-action in `.github/workflows/ci.yml`, with a comment saying Lake does not compile a module again when its restored output is up to date.
- The same change turns the run block of the step `Check the GraphemeBreakTest.txt theorem within 10 minutes` into a `set -eu` block that exits 1 if `.lake/build/lib/lean/SegmentationDev/Test/GraphemeBreakTestTheorem.olean` exists, then runs the timed `lake build --wfail`.
- The PR #82 body reports a local run: after the timed build, the guard exited 1 and named the `.olean` file; after `rm -rf .lake/build` and `lake build --wfail`, it exited 0.
- The step-order rule for builds within one run is in `docs/solutions/conventions/run-timed-lake-build-before-any-build-that-covers-its-modules.md`.
