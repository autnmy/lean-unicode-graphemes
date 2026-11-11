---
module: build
date: 2026-11-11
problem_type: developer_experience
component: tooling
severity: medium
audience: both
related_components:
  - testing_framework
tags:
  - lake
  - lean
  - lakefile
  - test-driver
applies_when:
  - Adding a new module under Segmentation/ or SegmentationTest/
  - Splitting test checks into modules the test driver imports
---

# A Lake module builds only when imported, and imports need an owning library

## Context

`lakefile.toml` declares the `Segmentation` library with no `globs`. Lake then builds only the modules reachable by imports from its root, `Segmentation.lean`. A new file such as `Segmentation/Statements.lean` is not compiled at all until something imports it, so `lake build` stays green even if the file has errors.

The test driver `SegmentationTest.lean` is the root of a `lean_lib`-less executable. Lake resolves an import only to a module that some library of the package owns. So `import SegmentationTest.Statements` fails unless a library claims that module.

## Solution

- Import each new library module from the root: `Segmentation.lean` gains `import Segmentation.Statements`.
- For check modules under `SegmentationTest/`, declare a library that owns them without adding a root of its own:

```toml
[[lean_lib]]
name = "SegmentationChecks"
roots = []
globs = ["SegmentationTest.+"]
```

Then import the check module from `SegmentationTest.lean`, so `lake test` elaborates it and a failed check stops the build.

## Why it matters

Both failures are quiet or far from the cause. A module that is never imported is never checked, so a broken statement file can sit in the tree under a green build. An import with no owning library fails to resolve, and the fix is in `lakefile.toml`, not in the file that reports the error.

## Evidence

- PR #11 adds `import Segmentation.Statements` to `Segmentation.lean`.
- PR #11 adds the `SegmentationChecks` library to `lakefile.toml`, with the comment that the test driver imports the checks and Lake resolves an import only to a module some library of the package owns.
- PR #11 adds `import SegmentationTest.Statements` to `SegmentationTest.lean`, whose module comment says importing it makes `lake test` elaborate the checks.
