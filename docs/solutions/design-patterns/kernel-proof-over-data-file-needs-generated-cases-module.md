---
module: SegmentationDev.Test
date: 2026-11-13
problem_type: design_pattern
component: testing_framework
severity: medium
audience: both
related_components:
  - tooling
  - development_workflow
tags:
  - decide-kernel
  - generated-data
  - drift-check
  - conformance-test
applies_when:
  - Proving in the kernel that code agrees with every line of an external data or test file
  - Turning a runtime IO check into a theorem
---

# Prove agreement with a data file through a generated, drift-checked cases module

## Context

The kernel cannot read a file. A theorem saying "`graphemes` matches every line of `GraphemeBreakTest.txt`" therefore needs the file's lines as Lean terms. Once the lines are copied into Lean, the theorem is only about that copy. Three gaps open up: the copy can drift from the file, a shorter copy can still prove a "for all cases" statement, and deciding through `String` is slow in the kernel.

## Solution

Close each gap at the step that causes it:

1. **Generate the copy, do not write it by hand.** The generator (`lake exe gen-tables`) parses the file and writes only the parsed cases, not the comments, to `SegmentationDev/Test/GraphemeBreakTestData.lean`. The renderer `renderCasesModule` refuses a file whose parsed count disagrees with its `# Lines:` trailer, so a truncated file never becomes proof data.
2. **Drift-check the copy byte for byte.** `lake test` runs `checkCommittedTestData`, which compares the committed module with what the renderer makes of the file now. The CI generator step adds the module's path to its `git status --porcelain` check. An expect-failure check drops line 840 and confirms the drift check fails.
3. **Put the count inside the decided Bool.** `linesMatch` is `cases.length == expectedLineCount && (mismatches segment cases).isEmpty`. Without the count, an empty or truncated list makes the "every case matches" part true for free.
4. **Decide over the cheap core, then bridge.** The kernel decides `linesMatch coreClusters cases`, where `coreClusters` calls the `List Char` function `clustersOf` directly. A separate lemma, `clusters_eq_coreClusters`, is proved by `simp` for every input, not decided per case. It turns the decided result into a statement about the public `graphemes` wrapper.

Build a case from its clusters only (`GraphemeBreakCase.ofClusters` sets `codePoints := expected.flatten`), so the input and the expected output in the data can never disagree.

## Why it matters

The theorem is only as good as the claim that its data is the file. If any of these parts is missing, the proof still checks, but it proves something weaker than the README says. Deciding through `String.ofList` and `String.toList` would spend most of the kernel time on UTF-8 encoding. The bridge lemma avoids that cost without weakening the statement.

## Evidence

PR #30:
- `SegmentationDev/Test/GraphemeBreakTestFile.lean` adds `ofClusters`, `casesModulePath` and `renderCasesModule`, which calls `checkCounts` before rendering. Its section comment explains that the kernel cannot read a file and that only parsed cases are written.
- `SegmentationDev/Test/DataChecks.lean` adds `checkCommittedTestData` and the expect-failure check built on `casesModuleWithoutLine840`.
- `.github/workflows/ci.yml` adds `SegmentationDev/Test/GraphemeBreakTestData.lean` to the generator drift step.
- `SegmentationDev/Test/GraphemeBreakTestTheorem.lean` defines `linesMatch` with the count, `coreClusters`, the lemma `clusters_eq_coreClusters`, and the theorem `graphemes_match_graphemeBreakTest`. It also proves `linesMatch coreClusters [] = false`.
- `SegmentationDev/Test/GraphemeBreakTestTheoremTests.lean` shows the decided check is false on a one-case list even when that case matches.
