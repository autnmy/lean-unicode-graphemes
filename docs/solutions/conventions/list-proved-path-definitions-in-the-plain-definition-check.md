---
module: SegmentationDev.Test
date: 2026-11-15
problem_type: convention
component: testing_framework
severity: medium
audience: both
related_components:
  - Segmentation.Slice
  - SegmentationDev/Test/SliceAgrees.lean
tags:
  - partial-def
  - implemented-by
  - extern
  - axiom-gate
  - run-tac
applies_when:
  - Adding a definition that a headline theorem's proof unfolds
  - Relying on the axiom gate to show that the code that runs is the code that was proved
---

# List every proved-path definition in a plain-definition check

## Context

A headline theorem says something about the code only if the code that runs is the definition the proof unfolds. Three things break that link. A `partial def` is stored as an opaque constant, so a proof cannot unfold it. An `implemented_by` or `extern` attribute swaps in other code at run time. None of them adds an axiom, so the `#assert_axioms` gate stays green. The keyword scan rejects `implemented_by` and `extern` as words, but it does not look for `partial`.

## Solution

For each new definition on a proved path, add its name to a `run_tac` check that requires three things: `env.find?` returns `.defnInfo`, `Compiler.getImplementedBy?` is `none`, and `isExtern` is false. PR #77 does this in `SegmentationDev/Test/SliceAgrees.lean` for `sliceGraphemes`, `sliceBoundaries`, `charProps`, `asciiProps`, `scanClusters` and `clusterBounds`. Include internal helpers, not only the public entry points.

The list is explicit, so a new helper is not covered until someone adds it. When you add a definition the proof unfolds, add it to the list in the same change.

## Why it matters

A passing axiom gate reads as "the scanner is proved". If a helper becomes `partial` or gains a compiled substitute, that reading is wrong and no other check in CI fails. The plain-definition check is the only guard against `partial`.

## Evidence

- PR #77 adds `slice_scanner_definitions_are_plain_with_no_compiled_substitute` in `SegmentationDev/Test/SliceAgrees.lean`. Its comment says a `partial` definition is opaque, a compiler substitute is recorded as an attribute, neither shows up as an axiom, and the keyword scan does not look for `partial`.
- The same check lists the six definitions of `Segmentation/Slice.lean`, internal `scanClusters` and `clusterBounds` included.
- Issue #70 explains that a `partial def` has no equation lemmas, so the proof cannot unfold it, and lists the forbidden words the keyword scan rejects, which do not include `partial`.
