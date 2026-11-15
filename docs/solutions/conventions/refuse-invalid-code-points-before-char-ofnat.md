---
module: SegmentationDev.Test
date: 2026-11-12
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - SegmentationDev.TableGen
tags:
  - lean
  - char-ofnat
  - surrogate
  - code-point
  - parsing
applies_when:
  - Code reads a hex code point from a text file and later turns it into a Lean Char
---

# Refuse invalid code points before they reach Char.ofNat

## Context

Unicode data files name code points in hex, such as `1F1E6`. A parsed hex number is not always a valid Lean `Char`: surrogates (`D800` to `DFFF`) and values above `10FFFF` are not. The comment on `codePoint?` in this change records that `Char.ofNat` does not fail on such a value; it quietly turns it into U+0000.

## Solution

Check the number with `Nat.isValidChar` right after parsing, and treat an invalid value as a parse error:

```lean
def codePoint? (token : List Char) : Option Nat := do
  let n ← parseHex? token
  if decide n.isValidChar then some n else none
```

In `parseTestFile` this makes the whole line an error that names its line number. Test it with a surrogate (`D800`) and with `110000`, each placed after a valid line.

## Why it matters

If the value reaches `Char.ofNat` unchecked, the test runs the code on U+0000 instead of the code point the file names. The test may then pass or fail for the wrong reason, and the output gives no sign of the swap.

## Evidence

- PR #16 adds `codePoint?` in `SegmentationTest/GraphemeBreakTestFile.lean` (now `SegmentationDev/Test/GraphemeBreakTestFile.lean`), with the comment that surrogates and values past U+10FFFF are refused because `Char.ofNat` would turn them into U+0000.
- `SegmentationDev/Test/GraphemeBreakTestFileTests.lean` in the same change proves, with `decide +kernel`, that `parseTestFile` rejects a line holding `D800` and a line holding `110000`, each after a valid line.
