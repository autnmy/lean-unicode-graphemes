---
module: SegmentationDev.Test
date: 2026-11-12
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - Segmentation.graphemes
  - Segmentation.boundaries
tags:
  - lean-string-escape
  - grapheme-break-test
  - code-points
  - test-helpers
applies_when:
  - A test needs text that contains code points above U+FFFF, such as regional indicators or emoji
  - Copying lines of data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt into Lean checks
---

# Write test text above U+FFFF as Nat code point lists, not string literals

## Context

GraphemeBreakTest.txt prints each test line as hex code point numbers, for example `1F1E6 × 1F1E7`. Many of the interesting lines (GB11 emoji sequences, GB12/GB13 regional indicators) use code points above U+FFFF. Lean's `\u` string escape takes exactly four hex digits. So a string literal cannot spell U+1F1E6, and the plan's assumption that `\u{…}` escapes would work did not hold.

## Solution

Use the helpers in `SegmentationDev/Test/GraphemeBreakTestLine.lean`. They take the code point numbers exactly as the file prints them:

```lean
def text (cps : List Nat) : String := String.ofList (cps.map Char.ofNat)
def clusters (cps : List Nat) : List (List Nat) :=
  (Segmentation.graphemes (text cps)).map fun g => g.toList.map Char.toNat
def cuts (cps : List Nat) : List Nat := Segmentation.boundaries (text cps)
```

A guard then reads like the file line:

```lean
#guard clusters [0x1F1E6, 0x1F1E6] == [[0x1F1E6, 0x1F1E6]]
```

Write the expected side as a hand-copied `Nat` list too. Never compute it through the segmenter or the property tables.

## Why it matters

If you try a string literal, the build fails, or you end up skipping the astral lines. Those lines are the only file evidence for GB11 and GB12/GB13. Writing both sides as code point numbers keeps each guard checkable by eye against the cited line. It also keeps the expected value independent of the code under test.

## Evidence

- PR #14 adds `SegmentationDev/Test/GraphemeBreakTestLine.lean`. Its module docstring says the `\u` escape takes exactly four hex digits, so code points above U+FFFF cannot be written in a string literal. It defines the `text`, `clusters` and `cuts` helpers.
- `SegmentationDev/Test/GraphemesRegionalIndicatorRules.lean` and `SegmentationDev/Test/GraphemesEmojiZwjRule.lean` in PR #14 write their GraphemeBreakTest.txt lines (for example lines 321 and 846) as `Nat` lists through those helpers.
