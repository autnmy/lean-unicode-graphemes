---
module: ci
date: 2026-11-11
problem_type: convention
component: development_workflow
severity: medium
audience: both
related_components:
  - documentation
tags:
  - sha256
  - ci
  - frozen-file
  - github-actions
applies_when:
  - A file must not change unless a recorded SHA-256 changes with it in plain view
  - A CI step reads a digest line out of README.md or another document
---

# Pin a frozen file with exactly one checked SHA-256 line

## Context

`Segmentation/Statements.lean` holds the theorem statements the library's proofs must meet. They are fixed before the code exists, so they cannot be bent to fit it. `README.md` records the file's SHA-256, and CI fails when the file and the recorded digest differ. Then any change to the statements must also change the README line, where a reviewer sees it.

The easy version of this check is `grep ... README.md | sha256sum --check`. It has a gap. The grep filters lines, so a digest line that is missing, written twice, or malformed (for example uppercase hex) is dropped or checked twice. The check can then pass without checking what it was meant to check.

## Solution

Keep the digest in the tool's own format: one line of 64 lowercase hex characters, two spaces, then the path. Then do three things in the CI step:

1. Select lines with a strict, anchored pattern: `^[0-9a-f]{64}  Segmentation/Statements\.lean$`.
2. Count the matches and fail unless there is exactly one.
3. Pipe that one line to `sha256sum --check --strict`.

Run the step right after checkout and before the build action. Then it hashes the bytes git checked out, before any build step writes to the tree. Set `LC_ALL: C` so the character class means plain ASCII hex.

The workflow holds no copy of the hash. `README.md` is the one place the digest lives, and the same command in the README lets anyone run the check locally.

## Why it matters

The point of a frozen file is that changing it is loud. If the check can pass with zero or two digest lines, someone can delete or duplicate the line and change the file quietly. Requiring exactly one match turns each of those edits into a red build. Using the `sha256sum` check format means no custom parsing to get wrong.

One gap stays open: the digest is over the bytes git stores. A local Windows checkout that converts line endings will fail the check locally only; CI on Ubuntu is not affected.

## Evidence

- PR #11 adds the step "Check the theorem statements against their recorded SHA-256" to `.github/workflows/ci.yml`, placed before `leanprover/lean-action`. Its comment says a missing, duplicated or malformed line fails "instead of checking nothing". The step counts matches with `grep -cE`, exits 1 unless the count is 1, then runs `sha256sum --check --strict`.
- PR #11 adds the "Theorem statements" section to `README.md`, holding the single digest line for `Segmentation/Statements.lean` and the same command for a local check.
