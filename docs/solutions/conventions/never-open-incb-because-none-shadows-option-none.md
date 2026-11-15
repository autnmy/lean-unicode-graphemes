---
module: Segmentation
date: 2026-11-15
problem_type: convention
component: statements
severity: medium
audience: both
related_components:
  - tables
  - tests
tags:
  - lean-naming
  - incb
  - gcb
  - option-none
  - name-resolution
applies_when:
  - Writing code or tests that use `InCB` or `GCB` constructors
  - Adding an `open` for a property type to shorten names
---

# Never `open InCB`: `InCB.none` would hide `Option.none`

## Context

PR #56 renamed the property constructors to lowerCamelCase. `InCB` now has `consonant extend linker none`, and `GCB` has `cr lf control extend zwj regionalIndicator ...`. A constructor named `none` shares its short name with `Option.none`. Also, `extend` now exists in both types.

## Solution

- Do not write `open InCB` anywhere. Write `.none` only where Lean already expects an `InCB`, such as `Range.lookup .none incbRanges` or a `Props` field `incb := .none`. Write `InCB.none` elsewhere.
- `open GCB in` is still used for `rules` and `breakRows`, so a bare `extend` there means `GCB.extend`. Reach the InCB value through dot syntax under an expected type, such as `incbIs .extend` or `incbIs .linker`.
- Do not add an alias, `abbrev` or `export` for an old name. An alias would let a missed call site keep compiling, and it would change the hash-pinned `Segmentation/Statements.lean` beyond names and docstrings.

## Why it matters

If `InCB` were opened, `none` in nearby code would stop meaning `Option.none`. Code that pattern-matches or returns an `Option` could then fail with confusing type errors. Worse, it could pick the wrong constant where both would type-check. The rule is not visible from any single file, so an edit made for convenience could break it.

## Evidence

- Issue #51, which PR #56 closes, states the rule: never `open InCB`, because `InCB.none` would then shadow `Option.none`. This change does not demonstrate the shadowing itself; the claim comes from the issue.
- PR #56 follows the pattern. `Segmentation/Tables.lean` and `Segmentation/TableLookup.lean` use `.none` where the type is `InCB`. Tests such as `SegmentationDev/Test/GraphemesCoreStubProps.lean` write `InCB.none`. `Segmentation/Statements.lean` keeps `open GCB in` for `rules` and writes `incbIs .linker` and `incbIs .extend`.
