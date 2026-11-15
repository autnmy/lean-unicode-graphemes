---
module: SegmentationDev.Test
date: 2026-11-13
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - SegmentationDev.Gate.Axioms
  - SegmentationDev.Gate.KeywordScan
tags:
  - table-driven-tests
  - exact-equality
  - axiom-gate
  - keyword-scan
applies_when:
  - Adding or changing a test of SegmentationDev.Gate.disallowedAxioms or SegmentationDev.Gate.findForbidden
  - Merging overlapping test files into one table
---

# Compare the exact result list in one table per gate unit

## Context

The axiom gate (`SegmentationDev.Gate.disallowedAxioms`) and the forbidden-word scanner (`SegmentationDev.Gate.findForbidden`) were once tested in twenty files. Several files asserted the same input, but with different strictness. Some used `==`. Others used `contains`, a length check, or `isEmpty`. A `contains` check passes even when the gate reports words or axioms it should not. So the weaker copies could keep passing after the behaviour broke, and only the stricter copies would notice.

## Solution

Keep one test file per unit, with one table of `(input, expected)` rows:

- `SegmentationDev/Test/DisallowedAxioms.lean` for the axiom gate.
- `SegmentationDev/Test/FindForbiddenScansInterpolation.lean` for words inside `s!` and `m!` braces.
- `SegmentationDev/Test/FindForbiddenProse.lean` for comments, strings and «…» names.
- `SegmentationDev/Test/FindForbiddenWords.lean` for each word and its line.

Each file loops over its rows with `unless got == expected do throwError ...`. Every row states the full expected list, including `[]` for clean inputs. No `contains`, length or `isEmpty` checks.

Add a new case as a row in the matching table, not as a new file. Merge two rows only when the inputs are byte-identical. Inputs that differ only in a name stay separate rows, for example `Gate.madeUpAxiomForThisTest` and `Gate.madeUpAxiomForTest`. Do not join single-line sources into one multi-line source, or split one apart. That changes what the scanner reads and which line numbers it reports.

Exact equality is safe for the axiom gate because its result keeps the order of its input. The comment in `DisallowedAxioms.lean` records this.

## Why it matters

With one table, a change to the gate's contract needs one edit per behaviour, and no copy can keep a weaker check. An exact list also catches a gate that reports too much, not only one that reports too little.

## Evidence

- PR #29 deletes nineteen files and merges their inputs into the four tables above. `SegmentationDev/Test.lean` imports the four merged files in place of the nineteen deleted ones. The driver still imports other test modules, such as AxiomChecker, AllowedAxiomsList and FindForbiddenStringForms.
- In PR #29, the deleted `SegmentationTest/KeywordScanCodeAfterComment.lean` and `SegmentationTest/KeywordScanInterpolatedSorry.lean` checked `found.contains (1, "sorry")`. Their inputs are now rows compared with `==` in `SegmentationDev/Test/FindForbiddenProse.lean` and `SegmentationDev/Test/FindForbiddenScansInterpolation.lean`.
- In PR #29, the deleted `SegmentationTest/AxiomCheckerDisallowed.lean` and `SegmentationTest/AxiomGateDisallowedMixed.lean` checked `bad.length == 2 && bad.contains ...`. Their shared five-axiom array is now one row in `SegmentationDev/Test/DisallowedAxioms.lean`, expecting exactly the list containing `sorryAx` and `Lean.ofReduceBool`.
- The header comment in `SegmentationDev/Test/DisallowedAxioms.lean` says the result keeps the order of the input, so each expected list is exact.
