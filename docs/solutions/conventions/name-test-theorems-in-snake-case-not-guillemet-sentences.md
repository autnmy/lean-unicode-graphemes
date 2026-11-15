---
module: SegmentationDev.Test
date: 2026-11-15
problem_type: convention
component: testing_framework
severity: low
audience: both
related_components:
  - keyword-scan
  - lake-test
tags:
  - naming
  - test-theorems
  - snake-case
  - forbidden-words
  - guard
applies_when:
  - Adding or renaming a test check under SegmentationDev/Test
  - Adding a test module whose file name would need «» to import
---

# Name test theorems in snake_case that states the result, not as «» sentences

## Context

The test checks under `SegmentationDev/Test` used to be named as whole sentences inside «», for example `theorem «linesMatch rejects an empty case list»`. Mathlib's naming convention instead asks for snake_case names that state the result. PR #65 renamed all of them, and moved `RangeLookupBoundaries.2.lean` to `RangeLookupBoundaries.lean`, because a dot in a module name forces a «» import.

Older learnings and code you copy from may still show the sentence style. Do not copy it.

## Solution

- Name each check in snake_case so the name says what is proved. Keep the camelCase of an identifier you refer to: `linesMatch_nil_eq_false`, `boundaries_empty_eq_singleton_zero`, `gcbOf_surrogates_other_and_1F1E6_regionalIndicator`.
- Put the explanation in the `--` comment above the check, which is where the sentence now lives.
- A check the kernel proves (`decide`, `decide +kernel`, `rfl`, a type ascription) stays a `theorem` or becomes an `example`. Never turn it into `#guard`, which only runs the code and gives no kernel proof. Use `#guard` only for checks that already evaluate a `Bool`.
- In tests that mention forbidden words (`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`), join every word of the name with `_`. Example: `axiom_gate_self_test_rejects_sorry_native_decide_and_user_axiom`. The keyword scan skips «» names as prose but scans plain names as code. It counts `_` as a word character, so the joined name is one word, while a forbidden word standing alone as a dotted name part fails CI.
- A type-pin theorem must not reuse the name of the lemma it pins when that name is reachable through `open Segmentation`. Add a word instead: `mem_cutsOf_type_holds_for_every_props`, `graphemes_rules_type_is_cutsMatchRules_props_graphemes`.
- Give test modules plain file names (no extra dots), so `SegmentationDev/Test.lean` imports them without «».

## Why it matters

A plain name is something a reader or a later proof can refer to, and it matches the rest of the library. The two hidden traps only show up once the «» is gone. First, the scanner starts reading the name as code, so a name like `rejects.sorry` fails the CI forbidden-word step. Second, a plain name can clash with a library lemma brought in by `open Segmentation`, which makes `lake test` fail. Demoting a kernel proof to `#guard` would pass every build but weaken the check without anyone noticing.

## Evidence

- PR #65 renames every `theorem «…»` under `SegmentationDev/Test`. For example, `SegmentationDev/Test/GraphemeBreakTestTheorem.lean` now has `linesMatch_nil_eq_false` and `mismatches_never_joining_segmenter_eq_line_840`, both still proved by `decide +kernel`.
- `SegmentationDev/Test/AxiomGateSelfTest.lean` in PR #65 names its check `axiom_gate_self_test_rejects_sorry_native_decide_and_user_axiom`, with the forbidden words joined by underscores.
- `SegmentationDev/Test/GraphemesRules.lean` in PR #65 names the pin of `mem_cutsOf` as `mem_cutsOf_type_holds_for_every_props`, so it does not reuse the library name under `open Segmentation`.
- PR #65 moves `SegmentationDev/Test/RangeLookupBoundaries.2.lean` to `SegmentationDev/Test/RangeLookupBoundaries.lean` and changes the import in `SegmentationDev/Test.lean` to `import SegmentationDev.Test.RangeLookupBoundaries`.
- Issue #53 states the scanner rules: «» names are skipped as prose, `_` counts as a word character, and a forbidden word standing as its own dotted name part is flagged. `SegmentationDev/Gate/KeywordScan.lean` is not part of this change. To confirm the rules, read that file.
