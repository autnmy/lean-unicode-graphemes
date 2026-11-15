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
  - wfail
  - warnings
  - lake-build
  - lean-action
applies_when:
  - Making compiler warnings fail CI
  - Adding a library, executable or test driver to lakefile.toml
  - Adding a CI step that runs lake test, lake exe or lake env lean
---

# Build every target by name with --wfail before lake test or lake exe runs

## Context

Lake's `--wfail` flag turns compiler warnings into errors. It applies only to the targets that one `lake build` command compiles. Plain `lake build` builds only `defaultTargets`, which here is `["Segmentation"]` in `lakefile.toml`. The development libraries and the three executables are outside it.

Other commands also compile code: `lake test`, `lake exe gen-tables`, and a setup action's own build. They compile whatever is not yet built, without the flag. So a warning in a test or a tool passes CI even when the main build carries `--wfail`.

## Solution

- Let the setup action only install the toolchain: `build: false` and `test: false` for `leanprover/lean-action`.
- Run each build as its own step with `--wfail` on the command line, so the flag shows in the CI log. The issue warns that an action may silently ignore an input it does not declare (this change does not confirm that); an explicit step puts the flag where the log shows it.
- Name the non-default targets in one `--wfail` build before anything runs them: `lake build --wfail SegmentationTableGen SegmentationChecks SegmentationGate segmentation-tests gen-tables keyword-scan`.
- Only then run `lake test`, `lake env lean ...` and `lake exe ...`, so they reuse modules already built with the flag.
- When you add a new library or executable, add it to that named build too.

## Why it matters

Without this, a warning in a test module or a tool never fails CI, and warnings build up in exactly the code that checks the library. The gap does not show: the main build line carries `--wfail` and looks complete.

Building a library by name also compiles modules no earlier step compiled. In this change, building `SegmentationChecks` reached a test that imported the keyword-scan executable root. The scanner's body moved into the library function `SegmentationDev.Gate.scanFiles` so the test could import it.

## Evidence

- PR #74 changes `.github/workflows/ci.yml`: the lean-action step goes from `build: true` / `test: true` to `build: false` / `test: false`, and new steps run `lake build --wfail`, the named-target build above, and then `lake test`.
- The added comment in `.github/workflows/ci.yml` says plain `lake build` builds only the Segmentation library, and the named build compiles the tests, generator and scanner with warnings as errors before any of them runs.
- The `lake build keyword-scan` line in the forbidden-words step becomes `lake build --wfail keyword-scan`.
- `SegmentationDev/Gate/KeywordScan.lean` gains `scanFiles`, `SegmentationDev/KeywordScan.lean` now only calls it, and `SegmentationDev/Test/KeywordScanMainExitCodes.lean` imports `SegmentationDev.Gate.KeywordScan` instead of the executable root.
