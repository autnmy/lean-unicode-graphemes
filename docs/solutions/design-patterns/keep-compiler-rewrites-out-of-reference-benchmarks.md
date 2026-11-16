---
module: Segmentation.Slice
date: 2026-11-16
problem_type: design_pattern
component: testing_framework
severity: medium
audience: both
related_components:
  - SegmentationDev.Test.ReferenceBreakDecisionUnchanged
  - BenchTest.OursIsReference
tags:
  - lean
  - csimp
  - benchmarks
  - reference-isolation
applies_when:
  - A proved fast definition coexists with a reference whose original algorithm must remain independently timed.
---

# Keep compiler rewrites out of reference benchmarks

## Context

Equal results do not imply equal execution costs. The benchmark must retain the original boundary decision even after the scanner gains a proved replacement.

`breaksBefore` is that reference decision. The slice scanner instead calls `breaksBeforeFast`, and `breaksBeforeFast_eq_breaksBefore` proves their results equal.

## Solution

Keep this equality as an ordinary theorem, without `@[csimp]`. That attribute registers a rewrite used during compilation. Rewriting the reference call to the fast decision would change the measured algorithm without editing the reference definition.

Select the fast decision explicitly at the scanner's call site. Use the equality locally in the agreement proof, as `scanClusters_agree` does:

```lean
simp only [hget, breaksBeforeFast_eq_breaksBefore]
```

Distinguish source checks from checks of compiled execution. A dependency walk through `.defnInfo` values and `getUsedConstants` reads stored definition bodies. Its success does not establish that compilation leaves those calls unchanged.

When adding compiler rewrites, check whether either side serves as an independently timed reference. Preserve that distinction before registering the rewrite. This restriction protects benchmark meaning; it is not a general ban on compiler simplification.

## Why it matters

A compiler rewrite can preserve every functional equality while changing what the reference column measures. The benchmark would then time the optimized decision where it promises the original one.

Checking compiler rewrites alongside source dependencies protects both obligations: equal segmentation results and distinct measured algorithms.

## Evidence

PR #93 adds the ordinary theorem `breaksBeforeFast_eq_breaksBefore` in `Segmentation/Slice.lean`, without `@[csimp]`. The same diff explicitly switches `scanClusters` to `breaksBeforeFast` and applies the equality locally in `scanClusters_agree`.

`SegmentationDev/Test/ReferenceBreakDecisionUnchanged.lean` follows `.defnInfo` bodies through `info.value.getUsedConstants` and rejects references to the fast decision. `bench/BenchTest/OursIsReference.lean` also adds `Segmentation.breaksBeforeFast` to its forbidden names. These changes establish the source-level separation; the diff contains no experiment registering a compiler rewrite.
