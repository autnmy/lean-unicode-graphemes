---
module: bench
date: 2026-11-16
problem_type: design_pattern
component: bench
severity: medium
audience: both
related_components:
  - bench/Main.lean
  - bench/BenchTest/ParseCommand.lean
tags:
  - rfl
  - dispatch
  - benchmark
  - wiring-test
  - equal-outputs
applies_when:
  - A function maps a case (such as a `Library` value) to one of several implementations that return the same results
  - A test must prove which implementation each case runs, not just that it returns the right answer
---

# Pin each dispatch arm by `rfl` when the implementations return equal outputs

## Context

The benchmark times two segmenters from this library: the reference and the fast slice scanner. They must return the same clusters on every input, or `lake exe bench check` fails. `Bench.clusterCountOf` in `bench/Main.lean` maps each `Library` case to the counter that the child process for that case times: `.ours` to `oursClusterCount` and `.fast` to `fastClusterCount`.

Because the two counters return equal counts on every input, no test that runs them can tell them apart. Suppose the `.ours` and `.fast` arms were swapped. The fast column and every pass-mark line would then report on the reference code, and every output test would still pass.

The first version of the test walked the constants used by `clusterCountOf`'s definition and checked that `fastClusterCount` was reached. That check also passes with the arms swapped, because the name is still reached, just from the wrong arm.

## Solution

Write one `rfl` theorem per arm, stating the exact value each case maps to:

```lean
theorem clusterCountOf_fast_is_fastClusterCount :
    Bench.clusterCountOf .fast = some Bench.fastClusterCount := rfl
theorem clusterCountOf_ours_is_oursClusterCount :
    Bench.clusterCountOf .ours = some Bench.oursClusterCount := rfl
theorem clusterCountOf_theirs_is_theirsClusterCount :
    Bench.clusterCountOf .theirs = some Bench.theirsClusterCount := rfl
```

`rfl` works here because `clusterCountOf` is a plain, non-recursive definition by cases. The kernel unfolds it and compares function constants by name. It never runs the counters, so equal outputs do not matter.

A reachability walk is still the right tool for a different question: whether one function, such as `Bench.fastClusters`, calls `Segmentation.sliceGraphemes` and never `Segmentation.clustersOf`. `bench/BenchTest/FastIsSlice.lean` does this. Use the walk for "does this one definition call X". Use one `rfl` per arm for "which case maps to which implementation".

## Why it matters

A swapped arm here gives no error. It produces a results file that labels reference timings as fast timings. The pass-mark lines would then judge the wrong code against UnicodeExtra. The same risk applies to any column, flag or mode that selects between implementations which agree by design. A test must pin the mapping itself, because the outputs never show it.

## Evidence

- PR #91 adds the three per-arm `rfl` theorems in `bench/BenchTest/ParseCommand.lean`, with the comment that each arm is pinned so swapping two of them fails. They replace an earlier walk over the constants used by `clusterCountOf`.
- The `.fast` arm `| .fast => some fastClusterCount` is added to `clusterCountOf` in `bench/Main.lean` in PR #91.
- A review of PR #91 pointed out that the walk passes with the `.ours` and `.fast` arms swapped. The author then swapped the arms in `bench/Main.lean` and rebuilt. `ParseCommand.lean` failed with `error: Not a definitional equality` at the `rfl` theorem, and built with exit 0 after the arms were put back.
- `bench/BenchTest/FastIsSlice.lean` in PR #91 keeps a walk over constants for the single-definition question, with a comment that the fast and reference clusters are equal on every input, so comparing outputs cannot show that the fast column runs the scanner.
