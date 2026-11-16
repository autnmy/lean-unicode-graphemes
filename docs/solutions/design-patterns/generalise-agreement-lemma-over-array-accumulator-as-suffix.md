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
  - tail-recursion
  - accumulator
  - agreement-proof
  - array
applies_when:
  - Rewriting a proved recursion that conses onto its recursive call into a tail loop with an Array accumulator
  - Re-proving an agreement lemma after adding an accumulator argument
---

# Generalise the agreement lemma over the accumulator as a suffix

## Context

In this case the scanner `scanClusters` built a `List` by consing each cluster onto its own recursive call. A call like that cannot be a tail call, so the compiled scanner used one stack frame per cluster. The fix adds an `acc : Array (ClusterBounds s)` argument and pushes each closed cluster onto it. Every recursive call is then a tail call.

The proof `scanClusters_agree` worked by induction on the text still to read. After the change, the loop's result also contains whatever `acc` already held. A lemma that compares the whole result to the reference fails at the inductive step, because the recursive call receives a longer `acc`.

## Solution

State the lemma for any `acc`, and say only what the loop appends:

```lean
∃ out : List (ClusterBounds s),
  (scanClusters s start pos start_le_pos state acc).toList = acc.toList ++ out ∧
  out.map (...) = (clustersOf.go ...).map String.ofList ∧
  ... :: out.map (·.stop.offset.byteIdx) = ...scanl ...
```

The claims that the old lemma made about the returned list now apply to `out`.

- **End case:** the witness is the one closing cluster, and `Array.toList_push` proves the first claim.
- **Break case:** call the induction hypothesis with `acc.push ⟨start, pos, _⟩`, which gives a list `out`. The witness is then `⟨start, pos, _⟩ :: out`. Rewrite with `Array.toList_push`, `List.append_assoc` and `List.singleton_append`.
- **Join case:** pass `acc` and the hypothesis's `out` through unchanged.
- **Caller:** apply the lemma with `acc := #[]`, and simplify `[] ++ out` with `List.nil_append`.

Make the consumers build their list once, with `Array.foldr`. Then prove one bridge lemma for each consumer, such as `sliceGraphemes_eq_map`, that turns the fold back into `toList.map`. Use `Array.foldr_toList` and `List.map_eq_foldr` for that rewrite. The theorems that depend on these consumers then prove with their statements unchanged.

## Why it matters

A tail loop is what makes long inputs safe. Without one, a long input can overflow the stack in compiled code. The suffix form keeps the old proof structure: you change the rewrites at each case, not the shape of the induction. The headline statements also stay unchanged, so a file whose bytes are pinned by a checksum, like `Segmentation/Statements.lean`, never has to change.

## Evidence

PR #95, in `Segmentation/Slice.lean`:

- It changes `scanClusters` to take and return `Array (ClusterBounds s)`.
- It restates `scanClusters_agree` with `∃ out, ... .toList = acc.toList ++ out`.
- It builds `sliceGraphemes` and `sliceBoundaries` with `Array.foldr`, and adds `sliceGraphemes_eq_map` and `sliceBoundaries_eq_map`.
- It applies the lemma with `#[]` in `sliceGraphemes_agree_clustersOf`.

The compiled check added to `SegmentationDev/Test.lean` segments a million letters followed by U+0301. It expects a bounds array of size 1000000 and a last cut at byte 1000002. The author's recorded `lake test` run reports it as PASS.
