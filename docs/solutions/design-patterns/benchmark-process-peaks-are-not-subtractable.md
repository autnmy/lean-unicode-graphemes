---
module: Benchmark memory measurements
date: 2026-11-15
problem_type: design_pattern
component: observability
severity: medium
audience: both
related_components:
  - bench/Bench/Measure.lean
  - bench/Bench/Report.lean
tags:
  - benchmarking
  - peak-resident-memory
  - memory-measurement
applies_when:
  - Comparing segmenter memory use with an input-only baseline
  - Changing how the benchmark collects or reports process peaks
---

# Report memory peaks without subtracting the baseline

## Context

The benchmark builds an input before running a segmenter. Its memory metric, `VmHWM` from `/proc/self/status`, records the process's peak resident memory. This is not a count of bytes allocated by segmentation.

An input-only process provides useful context, but its peak is not a quantity that can be subtracted to isolate segmentation.

## Solution

Keep the input-only baseline and each segmenter in separate processes. Report every measured peak (the baseline, this library's reference, UnicodeExtra and this library's fast segmenter) and state that each includes input generation.

Two processes can reach their peaks at different stages. Input generation can set both peaks even when segmentation later allocates memory. Subtracting those peaks can then report zero despite those allocations.

A shared process has a different problem: both libraries contribute to one lifetime peak. Reading that peak after each library does not give each library an independent measurement.

## Why it matters

A smaller reported difference does not establish fewer allocations. Treating peak differences as segmenter memory use can hide the effect a later optimization needs to measure.

Separate raw peaks do not isolate segmentation either. They preserve the actual measurement without giving a derived value a meaning it does not have. Keep that limit explicit when comparing implementations.

## Evidence

PR #55 adds `measureRow` in `bench/Bench/Measure.lean`. It records `baselinePeakKb`, `oursPeakKb` and `theirsPeakKb` from separate child processes without subtraction.

The `memoryMethod` text in `bench/Bench/Report.lean` states that each peak includes building the input. The new Memory paragraph in `README.md` documents the same boundary and the separate baseline.
