---
module: Segmentation.Statements
date: 2026-11-11
problem_type: convention
component: theorem_statements
severity: medium
audience: both
related_components:
  - testing_framework
tags:
  - lean
  - section-variables
  - theorem-statements
  - type-ascription
applies_when:
  - Editing the variable line in Segmentation/Statements.lean
  - Stating a theorem over parameters that later code supplies
---

# Section variable order is part of each statement's signature

## Context

`Segmentation/Statements.lean` states its theorems before the property lookup and the segmenter exist. It does this with one line: `variable (props : Char → Props) (graphemes : String → List String) (boundaries : String → List Nat)`.

In Lean, a definition takes only the section variables it uses, in the order the `variable` line declares them. So `JoinRestoresInput` and `ClustersNonEmpty` take only `graphemes`. `CutsMatchRules` takes `props` then `graphemes`. `BoundariesMatchCuts` takes `graphemes` then `boundaries`. Later proofs apply them in exactly these forms, for example `CutsMatchRules props graphemes`.

## Solution

Treat the order of the `variable` line as public signature. Pin each statement's parameters with a type ascription in the checks, so a reorder or a stray use fails the build next to the edit:

```lean
have _h2 : (Char → Segmentation.Props) → (String → List String) → Prop :=
  Segmentation.CutsMatchRules
```

Pin the one-parameter statements too. If `JoinRestoresInput` started to use `props`, it would demand a second argument, and its ascription would fail.

## Why it matters

The statements file is frozen by a SHA-256 check, and proofs are written against it later. A reorder changes no text inside any definition, so it is easy to miss in review. Without checks that apply each statement to typed arguments, either an ascription or a worked example, the break shows up only when a later proof fails to type-check, far from the edit. Worked examples such as `BoundariesMatchCuts (fun _ => ([] : List String)) (fun _ => [0])` also catch a reorder. The ascriptions give the most direct failure, because each one checks only the parameter list.

## Evidence

- PR #11 adds the `variable` line and the four statements in `Segmentation/Statements.lean`, then named `H1a`, `H1b`, `H2` and `H2'`. They are now `JoinRestoresInput`, `ClustersNonEmpty`, `CutsMatchRules` and `BoundariesMatchCuts`, and each docstring still opens with the old label.
- PR #11 adds `SegmentationTest/Statements.lean`, whose checks ascribe `JoinRestoresInput` and `ClustersNonEmpty` to `(String → List String) → Prop`, `CutsMatchRules` to `(Char → Segmentation.Props) → (String → List String) → Prop`, and `BoundariesMatchCuts` to `(String → List String) → (String → List Nat) → Prop`. Their comments say a different variable order or a stray parameter would make these ascriptions fail.
- The same file's worked example for `BoundariesMatchCuts` passes `(fun _ => ([] : List String))` then `(fun _ => [0])`. Its comment says the other order does not type-check.
