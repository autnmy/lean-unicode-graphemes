---
module: TableGen
date: 2026-11-12
problem_type: architecture_pattern
component: table_generation
severity: medium
audience: both
related_components:
  - Segmentation
  - Segmentation.Version
tags:
  - lake
  - code-generation
  - imports
applies_when:
  - Adding an import to TableGen or GenTables.lean
  - Moving a constant the generator reads
---

# The table generator must not import the generated tables

## Context

`Segmentation.lean` imports `Segmentation.Tables`, which imports the three generated modules under `Segmentation/Tables/`. If `TableGen` imported `Segmentation`, then a broken generated module (a bad hand edit, a half-finished write) would stop `TableGen` from building. The tool that rewrites the tables would then be unable to run.

The generator needs `unicodeVersion` to find `data/ucd/<version>/`. That constant used to live in `Segmentation.lean`.

## Solution

PR #12 moves `unicodeVersion` and `uax29Revision` unchanged into `Segmentation/Version.lean`, which imports nothing from the library. `Segmentation.lean` imports it, so `Segmentation.unicodeVersion` stays the one Lean definition of the version (CI and the README still write the data path out literally).

`TableGen/Ucd.lean` imports only `Segmentation.Statements`, `Segmentation.Version` and `Segmentation.Tables.Range`. None of those reach the generated modules. Keep it that way: when the generator needs another constant, put it in a module outside the generated import chain rather than importing `Segmentation`.

## Why it matters

Importing the top-level library is the easy choice and works fine while the tables are good. It fails only in the one situation the generator exists for, when the tables need to be rewritten.

## Evidence

- PR #12 adds `Segmentation/Version.lean`; its module comment says it imports nothing from the library so the generator can read the version without building the tables it writes.
- PR #12 removes the constants from `Segmentation.lean` and adds `import Segmentation.Version` and `import Segmentation.Tables` there.
- `TableGen/Ucd.lean` imports `Segmentation.Statements`, `Segmentation.Version` and `Segmentation.Tables.Range`, and defines `dataDir` from `Segmentation.unicodeVersion`.
