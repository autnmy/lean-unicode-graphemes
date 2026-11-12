---
module: SegmentationTest
date: 2026-11-12
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - Segmentation
tags:
  - lean
  - axioms
  - collect-axioms
  - sorry
  - compile-time-checks
applies_when:
  - A done condition says `#print axioms` on a theorem shows nothing beyond a fixed set of axioms
  - A test must fail when a proof is replaced by `sorry`
---

# Enforce an axiom rule with `collectAxioms`, not `#print axioms`

## Context

This library requires each proved theorem to depend only on `propext`, `Classical.choice` and `Quot.sound`. Issues often state this as "`#print axioms` on each shows nothing beyond …".

`#print axioms` only prints a message. It never fails elaboration. A test file that runs it passes under `lake test` even when the theorem is proved by `sorry`, or when it depends on a new `axiom`. So it checks nothing.

The obvious fix is to wrap the print in `#guard_msgs` and match the exact output. That test is too strict. It fails when a proof is rewritten and legitimately uses fewer axioms, for example when `Classical.choice` drops out.

## Solution

Read the axiom list with core's `Lean.collectAxioms` at compile time. Throw an error for any name outside the allowed list. This is a subset check, which is what the rule actually says.

```lean
open Lean in
theorem «graphemes_join uses no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let used ← collectAxioms ``Segmentation.graphemes_join
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    for ax in used do
      unless allowed.contains ax do
        throwError m!"Segmentation.graphemes_join depends on the disallowed axiom {ax}"
  trivial
```

Put one such check per theorem in a file under `SegmentationTest/`, and import that file from `SegmentationTest.lean`. Only `lake test` elaborates those files.

Put a type pin next to the check: a theorem whose stated type is the committed statement and whose body is the theorem under test. Then a renamed theorem, or one about a weaker statement, also fails the check.

## Why it matters

A proof by `sorry` depends on the axiom `sorryAx`. `sorryAx` is not in the allowed list, so the subset check fails the build. A test with `#print axioms` alone keeps passing. This rule is the only automatic guard that a "proved" theorem is really proved, so a check that cannot fail is worse than no check: it reports success.

The subset form also keeps the guard stable. A proof can change shape and use fewer axioms without anyone editing the test. Any new axiom, `sorry` included, still fails it.

## Evidence

- PR #15 adds `SegmentationTest/GraphemesPartition.lean`. Its two last theorems call `collectAxioms` on `Segmentation.graphemes_join` and `Segmentation.graphemes_ne_empty` inside `run_tac`, and they `throwError` on any axiom outside `propext`, `Classical.choice` and `Quot.sound`.
- The comment above those checks in the same file says that `#print axioms` only prints, and that a `sorry` proof depends on `sorryAx`, which is not in the allowed list.
- The same file pins each theorem's type with ascriptions to `Segmentation.H1a Segmentation.graphemes` and `Segmentation.H1b Segmentation.graphemes`.
- PR #15 changes `SegmentationTest.lean` to import `SegmentationTest.GraphemesPartition`, so `lake test` elaborates the checks.
