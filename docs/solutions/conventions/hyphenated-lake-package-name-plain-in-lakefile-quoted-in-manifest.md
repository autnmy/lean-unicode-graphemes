---
module: lakefile.toml
date: 2026-11-13
problem_type: convention
component: build_configuration
severity: low
audience: both
related_components:
  - lake-manifest.json
tags:
  - lake
  - package-name
  - lake-manifest
  - guillemets
  - rename
applies_when:
  - Renaming the Lake package or giving it a name that contains a hyphen
  - Reviewing a diff where lakefile.toml and lake-manifest.json spell the package name differently
---

# A hyphenated Lake package name is plain in lakefile.toml and «»-quoted in lake-manifest.json

## Context

Lake is the Lean build tool. It reads the package's settings from `lakefile.toml` and writes a second file, `lake-manifest.json`, that records the package name and its dependencies.

This package was renamed from `segmentation` to `lean-unicode-graphemes`. After the rename, the two files spell the name differently:

- `lakefile.toml`: `name = "lean-unicode-graphemes"`
- `lake-manifest.json`: `"name": "«lean-unicode-graphemes»"`

Lean uses the `«»` quotes to write a name that contains characters such as `-`. The lakefile already has a comment that says target names with a hyphen must be written in `«»`, or the lookup fails. That rule is about places that refer to a target, such as `testDriver`. It is not about the package's own `name` key.

## Solution

- Write the package `name` in `lakefile.toml` as a plain string, hyphens included. Do not add `«»` there.
- After you change the name, run Lake (`lake update`, or a build) so that it rewrites `lake-manifest.json`. Commit the file Lake writes.
- Do not hand-edit the manifest to remove the `«»`, and do not add them to the lakefile to make the two files look the same. The two spellings name the same package.
- Keep the `«»` rule for references to hyphenated targets, such as `testDriver`, as the lakefile comment says.

## Why it matters

The mismatch looks like a mistake, and the nearby comment points the wrong way. A reader who "fixes" one file by hand ends up with a manifest that Lake did not write. Letting Lake regenerate the manifest keeps one source of truth: the lakefile states the name, and Lake decides how to record it.

The rename did not change any library, executable or module name, so no `import` changed. A package rename and a module rename are separate steps.

## Evidence

- PR #33 changes `lakefile.toml` from `name = "segmentation"` to `name = "lean-unicode-graphemes"`, with no `«»`.
- In the same pull request, `lake-manifest.json` changes from `"name": "segmentation"` to `"name": "«lean-unicode-graphemes»"`.
- The PR body states that `lake update` regenerated `lake-manifest.json`, and that `lake build`, `lake test` and the other CI steps ran and exited 0 with the plain name. No check failed at the head commit e6668b489378dc5ff9c49f36db1cb8255cc2bde8.
- The context lines of the `lakefile.toml` diff show the comment saying that a target name with a hyphen has to be written in `«»` or the lookup fails.
