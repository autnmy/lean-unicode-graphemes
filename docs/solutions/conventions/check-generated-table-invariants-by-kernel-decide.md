---
module: Segmentation.TableLookup
date: 2026-11-12
problem_type: convention
component: tables
severity: medium
audience: both
related_components:
  - Segmentation.RangeLookup
  - Segmentation.Tables
tags:
  - decide
  - kernel
  - generated-tables
  - maxrecdepth
  - no-native-decide
applies_when:
  - A proof depends on a property of a generated table under Segmentation/Tables
  - A precondition is only written as a comment in generated code
---

# Prove generated-table invariants with kernel decide on a Bool check

## Context

The binary search `Range.lookup` needs its tables sorted with no overlapping ranges. Before PR #18, that rule was only a comment in the generated files, so nothing failed if a regenerated table broke it. This library bans `native_decide`, `sorry` and `axiom`, and the generated files must stay byte-for-byte unchanged. So the fact has to be checked by the kernel on the committed tables, without touching the generator.

## Solution

1. Write the rule as a `Bool` function and define the `Prop` as that function equal to `true`. The `Decidable` instance then comes for free:

```lean
def Range.Sorted {α : Type} (table : Array (Range α)) : Prop :=
  Range.chainOK table.toList = true

instance {α : Type} (table : Array (Range α)) : Decidable (Range.Sorted table) :=
  inferInstanceAs (Decidable (Range.chainOK table.toList = true))
```

2. Prove the rule for each committed table with `decide`, raising the recursion limit because the kernel walks every range:

```lean
set_option maxRecDepth 20000 in
theorem gcbRanges_sorted : Range.Sorted gcbRanges := by decide
```

3. Prove the generic theorem with the rule as a hypothesis (`Range.lookup_eq_scan`). Then state hypothesis-free corollaries per table (`gcbOf_eq_scan`, `extPictOf_eq_scan`, `incbOf_eq_scan`, `props_eq_scan`), so callers never carry the premise.

Put these modules directly under `Segmentation/`, not under `Segmentation/Tables/`, and import them from `Segmentation.lean`. Then `lake build` checks them, and they stay out of the generated tree.

## Why it matters

The `decide` proof turns a comment into a build failure. If the generator later emits an out-of-order or overlapping table, `lake build` fails at `Segmentation/TableLookup.lean` rather than leaving the search silently wrong. `decide` runs in the kernel, so the proof depends only on the standard axioms. `native_decide` would add `Lean.ofReduceBool`, which the library forbids.

## Evidence

- PR #18 adds `Segmentation/TableLookup.lean` with `gcbRanges_sorted`, `extPictRanges_sorted` and `incbRanges_sorted`, each `by decide` under `set_option maxRecDepth 20000 in`. Its module docstring says a regenerated table that is out of order or overlapping makes the build fail there.
- PR #18 defines `Range.Sorted` as `Range.chainOK table.toList = true` with an `inferInstanceAs` decidability instance in `Segmentation/RangeLookup.lean`.
- `SegmentationTest/TableLookupMatchesScan.lean` in PR #18 checks with `collectAxioms` that the three `_sorted` facts and the four corollaries use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The PR body reports that `lake build` and `lake test` both exited 0.
