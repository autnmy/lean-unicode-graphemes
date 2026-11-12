---
module: TableGen
date: 2026-11-12
problem_type: design_pattern
component: table_generation
severity: medium
audience: both
related_components:
  - SegmentationTest
  - Segmentation.Tables
tags:
  - unicode-data
  - code-generation
  - exhaustive-test
  - parser
applies_when:
  - A generator writes tables from data files and a test compares the tables with the same files
  - Adding a new property table or a new value name to TableGen/Ucd.lean
---

# A shared parser hides its own mistakes from the exhaustive table check

## Context

`lake exe gen-tables` reads the Unicode data files and writes the range tables. `lake test` then reads the same files and checks the table lookup for every code point U+0000..U+10FFFF. Both sides read the files through the same parsers in `TableGen/Ucd.lean`.

So the exhaustive check cannot catch one kind of bug. Suppose the parser maps the name `Extend` to `.SpacingMark`, or reads an unknown name as the default `Other`. Then the generator and the reference get the same wrong value, and all 1,114,112 comparisons still pass.

## Solution

Use these three rules together:

1. **Strict parsing.** Each of these inputs returns an error: a line the parser cannot read, a value name with no constructor, a code point past U+10FFFF, two entries that give one code point different values, and a file with no entries. None of them falls back to a default value, because a default would agree with itself on both sides.
2. **An independent reference path.** The generator runs the parsed entries through `normalize`, which sorts them, rejects conflicts and merges them. It then renders the modules, and the lookup does a binary search over them. The reference uses `paint`, which fills in one value per code point straight from the raw entries. `paint` shares no code with `normalize`, the rendered modules or `Range.lookup`. A bug in any of those that changes a value therefore shows up as a mismatch.
3. **Hand-written expectations for the parser.** For every value name the files use, a test parses one line and compares the result with a constructor written in the test. The constructor is not read from `gcbNames` or `incbNames`. File-backed spot checks then fix a known code point for several values, for example U+0300 is `Extend` and U+094D is InCB `Linker`.

When you add a property or a value name, add its name-to-constructor test and a spot check in the same change.

## Why it matters

An exhaustive check looks like proof, so reviewers rarely look past it. But it only proves that two computations agree. Both computations use the parser, so the parser needs its own checks, with expected values that come from outside the production code.

## Evidence

- PR #12 adds the parsers, `normalize` and `paint` in `TableGen/Ucd.lean`. Its module comment says that a default would give the same wrong answer on both sides.
- `SegmentationTest/DataChecks.lean` builds the reference with `paint` in `loadReference`, and `checkReferenceSpots` checks it against fixed values.
- `SegmentationTest/Ucd.lean` has one `#guard` for each Grapheme_Cluster_Break and InCB name, each against a constructor written in the test.
- `SegmentationTest/ParseGcbUnknownName.lean` and `SegmentationTest/ParseExtPictEmpty.lean` check that an unknown name and an empty file are errors.
