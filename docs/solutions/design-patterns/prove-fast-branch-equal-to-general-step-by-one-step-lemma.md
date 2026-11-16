---
module: Segmentation.Slice
date: 2026-11-16
problem_type: design_pattern
component: Segmentation.Slice
severity: medium
audience: both
related_components:
  - SegmentationDev.Test
tags:
  - lean
  - fast-path
  - ascii
  - step-lemma
  - agreement-proof
applies_when:
  - Adding a specialised branch, such as an ASCII path, to a scanner that is already proved equal to a reference
  - A fast branch skips a lookup, a decision or a state update that the general step performs
---

# Prove a fast branch equal to the general step with one step lemma

## Context

The scanner `scanClusters` had one path for every code point. It looked up the code point's properties with `charProps`, decided whether to break with `breaksBeforeFast`, and updated its state with `ScanState.push`. The proof that the scanner matches the reference `clustersOf.go` follows that one path.

An ASCII code point skips all three operations. Instead, `asciiBreaksBefore` makes the break decision from the previous code point's break class and the byte alone, and `asciiState` is the state that follows. If this branch gets its own induction, or its own inner loop, the agreement proof splits into two.

## Solution

Prove three facts, and only then touch the agreement proof:

1. `breaksBeforeFast_asciiProps : breaksBeforeFast s (asciiProps n) = asciiBreaksBefore s.prev.gcb n`, **for every state `s`**. This means the fast decision may ignore every look-back flag.
2. `ScanState.push_asciiProps : s.push (asciiProps n) = asciiState n`, again for every state. This means the fast state is exactly the state that `push` would leave.
3. A step equation, `scanClusters_step`. It says that, before the end of the slice, one unfolding of the loop equals the general step written with `charProps`, `breaksBeforeFast` and `push`. Its proof unfolds `charProps`, splits on `toNat < 128`, and rewrites the ASCII case with facts 1 and 2.

In the cons case of the agreement induction, `rw [scanClusters_step ...]` then replaces `rw [scanClusters]; split; · contradiction`. The ASCII branch needs no further change to the induction. Each branch still takes its tail call directly, so the loop keeps its speed.

The same change also edits the induction for a separate reason: the Array accumulator. `scanClusters_agree` gains an `acc` argument and an `out` witness for the clusters the scan appends, and its end case now uses `rw [scanClusters, dite_eq_left atEnd]`. Those edits come from the accumulator, not from the ASCII branch.

State facts 1 and 2 for every state, not for the states that tests try. A run of ASCII text can begin after any state, including one with a look-back flag set: a ZWJ, an InCB Linker, or an odd regional indicator. Rule GB9b is one case where the state matters. It joins a printable byte to a Prepend before it, so the first byte of a run can depend on the code point before the run.

## Why it matters

The step equation is the single place that ties the fast branch to the proved path. Without it, every change to the fast branch reopens the main induction. And a fast decision checked only on sample states can silently join or split clusters after an unusual state, for every caller that reaches the scanner through `@[csimp]`.

## Evidence

PR #95, in `Segmentation/Slice.lean`:

- It adds `asciiBreaksBefore` and `asciiState`, and proves `breaksBeforeFast_asciiProps` and `ScanState.push_asciiProps` for an arbitrary `ScanState`.
- It proves `scanClusters_step` by splitting on `(pos.get atEnd).toNat < 128`.
- In the cons case of `scanClusters_agree`, it rewrites with `scanClusters_step` in place of `rw [scanClusters]`, `split` and `contradiction`.
- It also adds the `acc` argument and `out` witnesses to `scanClusters_agree`, and its end case uses `rw [scanClusters, dite_eq_left atEnd]`.

`SegmentationDev/Test/AsciiBreaksBeforeRules.lean` checks the ASCII decision against `breaksBeforeFast` after armed ZWJ, Prepend, CR and regional-indicator states. `SegmentationDev/Test/SliceAsciiPathHandovers.lean` checks a Prepend (U+0600) before a run against the reference.
