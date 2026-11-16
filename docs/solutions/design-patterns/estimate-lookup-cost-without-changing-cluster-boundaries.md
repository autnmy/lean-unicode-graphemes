---
module: Grapheme benchmark
date: 2026-11-16
problem_type: design_pattern
component: benchmarking
severity: medium
audience: both
related_components:
  - Segmentation/Slice.lean
tags:
  - benchmarking
  - property-lookup
  - segmentation
applies_when:
  - Estimating property-lookup cost separately from the grapheme scanner
---
# Estimate lookup cost without changing cluster boundaries

## Context

Replacing Unicode properties with a constant does not isolate lookup cost in the grapheme scanner. Those properties also determine cluster boundaries and the state used for later decisions.

A changed boundary changes how many output elements the scan constructs. The timing difference therefore includes different segmentation and allocation work, not just the removed lookup.

## Solution

Keep the scanner's property values unchanged when measuring its total cost. Use profiling to attribute that cost, or estimate lookup cost in a separate loop that builds no clusters.

For the separate experiment:

1. Traverse the same input and call `Tables.propsLookup` for each non-ASCII code point.
2. Consume a field of each result in an accumulator so the lookup contributes to an observable result.
3. Compare with a loop that retains the same traversal and non-ASCII test but does no lookup.
4. Account for differences in accumulation work before attributing the timing difference to lookup.

Treat that difference as an estimate. Measure the unchanged full scanner separately to judge the actual optimization.

## Why it matters

A faster experiment can result from producing fewer clusters rather than finding properties faster. It can also become slower by producing more clusters. Either result can direct work toward the wrong cost.

This distinction matters whenever a value being replaced also controls later work. Removing the computation must not silently change the workload being compared.

## Evidence

PR #101 changes `Segmentation/Slice.lean`, where the non-ASCII branch of `scanClusters` binds `props := nonAsciiProps c`. It passes `props` to both `breaksBeforeFast` and `state.push`.

Within that branch, the boundary decision determines whether the scanner executes `acc.push (emit start pos start_le_pos)`. Replacing the properties therefore changes the decision's input as well as the next scan state. Any resulting boundary change also changes output construction.
