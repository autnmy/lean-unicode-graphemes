---
module: Benchmark build
date: 2026-11-15
problem_type: design_pattern
component: development_workflow
severity: medium
audience: both
related_components:
  - bench/build.sh
  - bench/build-self-test.sh
  - bench/Bench/Together.lean
  - bench/BuildFailureMain.lean
  - .github/workflows/bench.yml
tags:
  - ci
  - build-staging
  - compatibility
  - self-test
applies_when:
  - A job must publish "library A and library B cannot build together" as a fact
  - Harness code calls a third-party API that has not been compiled yet
---

# Stage builds so a library incompatibility is never confused with a harness bug

## Context

The benchmark must report, as a fact, when this library and UnicodeExtra cannot build on one toolchain. The adapter that calls UnicodeExtra was written without compiling it. One `lake build` of everything would fail the same way for a real incompatibility and for a wrong upstream name in the adapter.

## Solution

`bench/build.sh` builds in this order:

1. `bench-build-failure`, the reporter. It imports neither library, so it still builds when one of them fails.
2. `+Segmentation`, then `+UnicodeExtra`.
3. `+Bench.Together`, a module that holds only the two imports.
4. `Bench`, `bench`, `bench-tests`: the harness.

A failure in stages 2 or 3 writes the "cannot build together" results file and exits non-zero. A failure in stages 1 or 4 is a harness failure: it exits non-zero and writes nothing.

`bench/build-self-test.sh` puts a stand-in `lake` first on `PATH`, fails one target at a time, and checks the exit status and whether a results file appeared. The workflow runs it before the real build.

## Why it matters

The import-only module is the narrowest proof that the two libraries load together. Anything after it is the harness's own code. Without the stand-in test, a script that has only ever passed could label every failure the same way.

## Evidence

PR #55 adds `bench/build.sh` with `build_library` for `+Segmentation`, `+UnicodeExtra` and `+Bench.Together`, and `build_harness` for the rest. `bench/Bench/Together.lean` holds only `import Segmentation` and `import UnicodeExtra`. `bench/BuildFailureMain.lean` imports only `Bench.Measure`. `bench/build-self-test.sh` expects a results file for the three library targets and none for `bench-build-failure`, `Bench`, `bench` and `bench-tests`. The author ran it: all eight cases passed, and a copy of `build.sh` that treated UnicodeExtra as a harness stage failed with "results file no (want yes)".
