---
module: SegmentationDev.Test
date: 2026-11-13
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - SegmentationDev.Gate.KeywordScan
  - CI
tags:
  - keyword-scan
  - forbidden-words
  - string-interpolation
  - test-inputs
applies_when:
  - Writing a test whose input contains sorry, admit, axiom, native_decide, implemented_by, extern or unsafe
  - Writing an error message in a test of SegmentationDev.Gate.findForbidden
---

# Keep forbidden words in prose positions inside scanner tests

## Context

The forbidden-word scanner (`SegmentationDev.Gate.findForbidden`, run as `keyword-scan`) fails the build on `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` used as code. In CI it scans every `.lean` file in the repository, and that includes the test files that feed it those same words as inputs. The scanner skips prose: comments, plain string text and «…» names. It does not skip the `{…}` part of an `s!` or `m!` string, because that part is a Lean term.

## Solution

In a test file, put a forbidden word only in:

- a plain `"…"` string literal used as a test input,
- a `--` or `/- … -/` comment,
- a «…» theorem name.

In an error message such as `throwError m!"…"`, interpolate only bindings, for example `{repr src}` or `{repr got}`. Never write a forbidden word between the braces. Build multi-line inputs from plain literals joined with `++`, not from interpolated strings.

## Why it matters

If a test file uses a forbidden word as code, the scan fails on the test file itself, and the failure does not point at the test's purpose. The braces case is easy to miss: a word inside an `m!` message looks like message text, but the scanner reports it.

## Evidence

- In PR #29, `SegmentationTest/FindForbiddenScansInterpolation.lean` (now `SegmentationDev/Test/FindForbiddenScansInterpolation.lean`) has rows where a word inside `s!` or `m!` braces is reported, for example the `s!"{(show Nat from by sorry)}"` input expecting `[(1, "sorry")]`, while text outside the braces expects `[]`.
- `SegmentationTest/FindForbiddenProse.lean`, `SegmentationTest/FindForbiddenWords.lean` and `SegmentationTest/FindForbiddenScansInterpolation.lean` in PR #29 (now under `SegmentationDev/Test/`) each state in a comment that the inputs are plain string literals, so the scan of the file itself sees no code use. Their error messages interpolate only `repr` of bindings.
- The PR #29 description reports that the CI keyword step, scanning every `.lean` file outside `.lake`, checked 79 files and found no forbidden words.
