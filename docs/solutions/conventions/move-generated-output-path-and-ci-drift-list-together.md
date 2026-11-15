---
module: SegmentationDev.Test
date: 2026-11-15
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - SegmentationDev.Test.GraphemeBreakTestFile
  - CI
tags:
  - generated-files
  - drift-check
  - module-move
applies_when:
  - Moving or renaming a file that lake exe gen-tables writes
  - Changing casesModulePath or the generated= list in .github/workflows/ci.yml
---

# Move a generated file's path in the generator and in the CI drift list together

## Context

CI has a drift check: it runs `lake exe gen-tables` and then fails if `git status --porcelain` shows a change in the generated files. The check exists so committed generated files cannot fall out of step with the data files. Which files it watches is a hand-written list, `generated=` in `.github/workflows/ci.yml`. Where the GraphemeBreakTest cases are written is a separate value, `casesModulePath` in `SegmentationDev/Test/GraphemeBreakTestFile.lean`. Nothing ties the two together.

## Solution

When a generated file moves, change in the same commit:

- `casesModulePath` (or the table path the generator uses),
- the `import`, `namespace`, `open` and `end` strings the renderer emits, if the module name changes,
- the `generated=` list in the CI drift step.

Then run `lake exe gen-tables` and confirm `git status --porcelain -- Segmentation/Tables SegmentationDev/Test/GraphemeBreakTestData.lean` prints nothing. Also open the `generated=` list and check that each path in it is a file the generator really writes.

## Why it matters

If only the generator moves, it writes the new file, and the old committed file sits unchanged at a path the generator no longer touches. The drift check then watches the old path, sees no change, and passes. The check stays green while it checks nothing. No test points at the forgotten edit, so only a reviewer comparing the two paths would catch it. The byte check in `lake test` reads `casesModulePath`, so it follows the generator; only the CI list needs the manual edit.

## Evidence

- PR #42 changes `casesModulePath` in `SegmentationDev/Test/GraphemeBreakTestFile.lean` from `"SegmentationTest" / "GraphemeBreakTestData.lean"` to `"SegmentationDev" / "Test" / "GraphemeBreakTestData.lean"`, and changes the emitted import, namespace, open and end strings.
- The same pull request changes `.github/workflows/ci.yml` from `generated="Segmentation/Tables SegmentationTest/GraphemeBreakTestData.lean"` to `generated="Segmentation/Tables SegmentationDev/Test/GraphemeBreakTestData.lean"`.
- The regenerated `SegmentationDev/Test/GraphemeBreakTestData.lean` differs from the old file only in those import, namespace, open and end lines.
