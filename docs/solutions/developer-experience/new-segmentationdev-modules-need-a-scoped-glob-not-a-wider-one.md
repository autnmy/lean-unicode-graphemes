---
module: lakefile
date: 2026-11-15
problem_type: developer_experience
component: development_workflow
severity: medium
audience: both
related_components:
  - lakefile.toml
  - SegmentationDev
tags:
  - lake
  - lakefile
  - globs
  - exe-roots
applies_when:
  - Adding a development module directly under SegmentationDev/ rather than under Test/ or Gate/
  - Editing a globs entry in lakefile.toml
---

# Do not widen the `SegmentationDev` globs; give a new module its own library entry

## Context

All development code now lives under the `SegmentationDev` module root. Three modules sit directly under it and each defines `main`: `SegmentationDev.Test`, `SegmentationDev.GenTables` and `SegmentationDev.KeywordScan`. They are the roots of the `segmentation-tests`, `gen-tables` and `keyword-scan` programs.

Lake resolves an import only to a module that some library of the package owns. The libraries claim development modules with narrow globs: `SegmentationDev.Test.+` and `SegmentationDev.Gate.+`. In a Lake glob, `X.+` matches the submodules of `X` only, not `X` itself. So the exe roots stay out of every library, as the lakefile comment requires.

## Solution

- Put new test modules under `SegmentationDev/Test/` and new gate modules under `SegmentationDev/Gate/`. The existing globs then own them.
- For a new development module that belongs under neither, add a library entry that names it, the way `SegmentationTableGen` uses `roots = ["SegmentationDev.TableGen"]`.
- Do not write `globs = ["SegmentationDev.+"]`. That pattern also matches the three exe roots, which the lakefile comment says must stay out of every library.

## Why it matters

An import of a module that no library owns fails to resolve. Widening the glob to the whole root is the quickest edit that makes that error go away. But it moves the `main`-defining exe roots into a library, against the layout this lakefile relies on. Only a comment records that rule; no check enforces it.

## Evidence

- PR #42 adds a comment to `lakefile.toml` saying the globs end in `.+`, which matches submodules only, so the exe roots `SegmentationDev.Test`, `SegmentationDev.GenTables` and `SegmentationDev.KeywordScan` each define `main` and stay out of every library.
- The same `lakefile.toml` sets `globs = ["SegmentationDev.Test.+"]` for `SegmentationChecks`, `globs = ["SegmentationDev.Gate.+"]` for `SegmentationGate`, and `roots = ["SegmentationDev.TableGen"]` for `SegmentationTableGen`.
- The exe roots in that file are `root = "SegmentationDev.Test"`, `root = "SegmentationDev.GenTables"` and `root = "SegmentationDev.KeywordScan"`.
