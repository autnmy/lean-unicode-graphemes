---
module: SegmentationDev.Gate.Axioms
date: 2026-11-12
problem_type: convention
component: tooling
severity: medium
audience: both
related_components:
  - testing_framework
tags:
  - native-decide
  - axioms
  - ofreducebool
  - toolchain
applies_when:
  - Writing tests, messages or comments about which axiom native_decide produces
  - Matching axiom names in a gate or self-test
---

# On this toolchain, `native_decide` adds its own axiom

## Context

It is common to say that a proof by `native_decide` depends on `Lean.ofReduceBool`. That is not true on the pinned toolchain, `leanprover/lean4:v4.35.0`. Here the tactic adds a new axiom for each use, named like `t._native.native_decide.ax_1_1`, and the proof depends on that axiom.

The gate in `SegmentationDev/Gate/Axioms.lean` still rejects it, because it allows only `propext`, `Classical.choice` and `Quot.sound`. Any other name fails. The risk is in the text around the gate. Tests and comments that said `native_decide` gives `Lean.ofReduceBool` sent readers to look for the wrong name.

## Solution

- Write axiom rules as an allow list. Do not use a deny list of known bad names. A deny list that names `Lean.ofReduceBool` would miss the per-use `native_decide` axioms.
- In unit tests of `disallowedAxioms`, use `Lean.ofReduceBool` only as an example of some other axiom outside the allowed three. Do not present it as the output of `native_decide`.
- For a full test, plant a real `native_decide` proof in a temporary file. Match on text that contains `native_decide`, as `scripts/axiom-gate-self-test.sh` does.

## Why it matters

When the gate fails, its message names the axiom. A maintainer who expects `Lean.ofReduceBool` may not connect `t._native.native_decide.ax_1_1` to a `native_decide` call. The maintainer may also write a narrow check that misses the axiom. Check this again after a toolchain upgrade, because the axiom's name depends on the toolchain.

## Evidence

- The module comment in `Gate/Axioms.lean` (PR #23; now `SegmentationDev/Gate/Axioms.lean`) says that a proof that evaluates through the compiler depends on an axiom named like `t._native.native_decide.ax_1_1` on this toolchain.
- `scripts/axiom-gate-self-test.sh` (PR #23) says that `native_decide` adds an axiom of its own whose name contains `native_decide`, "rather than depending on `Lean.ofReduceBool`". It expects the gate's error to match `native_decide`. CI runs this script as the step "Check that the axiom check rejects forbidden axioms", and no check failed on the PR's head commit.
- `SegmentationDev/Test/DisallowedAxioms.lean` describes `Lean.ofReduceBool` as standing for any other axiom outside the allowed three.
