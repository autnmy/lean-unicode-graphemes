---
module: SegmentationDev.Test
date: 2026-11-12
problem_type: convention
component: testing_framework
severity: low
audience: both
related_components:
  - SegmentationDev.TableGen
tags:
  - parser
  - negative-test
  - test-design
applies_when:
  - Writing a test that a parser rejects an unknown value or malformed line
  - The parser also rejects input that yields no entries
---

# Test a rejected row next to a valid row

## Context

`parseEntries` in `SegmentationDev/TableGen/Ucd.lean` returns an error when a file yields no entries at all. That is useful: an empty or cut-off file must not become a table of defaults.

It also weakens tests. A theorem in `SegmentationDev/Test/Ucd.lean` feeds `parseGcb` a single line with the misspelled name `Regional_Indicatr` and expects an error. If the parser silently skipped that line, the result would be empty, the empty-result rule would fire, and the test would still pass. Code review on PR #12 pointed this out.

## Solution

When a test asserts that a parser rejects a bad row, put a valid row in the same input and assert that the whole parse fails:

```lean
#guard isError (SegmentationDev.TableGen.parseGcb "0041 ; Control # x\n1F1E6 ; Regional_Indicatr # x\n")
#guard isError (SegmentationDev.TableGen.parseIncb "0915 ; InCB; Consonant # x\n094D ; InCB; Linkr # x\n")
```

Keep the empty-input checks as separate tests, so each rule has a test that only it can satisfy.

## Why it matters

A test that passes for two reasons protects neither. If someone later relaxes the unknown-name rule to "skip the line", only the mixed input catches it.

## Evidence

- PR #12 adds the two mixed-input guards above to `SegmentationTest/Ucd.lean` (now `SegmentationDev/Test/Ucd.lean`), with a comment that the rejection must not depend on the parse ending up empty.
- `SegmentationDev/TableGen/Ucd.lean` `parseEntries` returns an error when no entries are found.
- A code review finding on PR #12 named the single-line rejection tests, now the theorems «parseGcb rejects a misspelled value name instead of falling back to Other» and «parseIncb rejects an unknown InCB value instead of defaulting to None» in `SegmentationDev/Test/Ucd.lean`. The mixed-input guards were added to answer it, and `SegmentationDev/Test/Ucd.lean` elaborated with both guards holding.
