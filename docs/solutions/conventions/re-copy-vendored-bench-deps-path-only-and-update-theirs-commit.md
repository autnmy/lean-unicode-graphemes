---
module: bench
date: 2026-11-16
problem_type: convention
component: tooling
severity: medium
audience: both
related_components:
  - ci
  - documentation
tags:
  - lake
  - vendoring
  - offline-build
  - benchmark
  - lake-manifest
applies_when:
  - Re-copying bench/vendor/UnicodeExtra or bench/vendor/UnicodeBasic from a newer upstream commit
  - Adding another vendored Lake package that must build with no network
---

# Re-copy vendored bench packages as path-only, and move the recorded commit with them

## Context

The benchmark package in `bench/` compares this library against UnicodeExtra. It must build with no network. So UnicodeExtra and its dependency UnicodeBasic are kept as source copies in `bench/vendor/`. Lake reaches them by local path, not by git. The README says the copies are re-made by hand to compare against a newer UnicodeExtra.

Two things make that re-copy easy to get wrong. First, a fresh upstream copy brings back its own git requires and its own `lake-manifest.json`, which pins those requires by git. Second, the UnicodeExtra commit shown in the benchmark results is now a constant typed into the workflow. Nothing checks it against the copy.

## Solution

When you re-copy, make every level path-only and update the recorded commit in the same commit:

1. In `bench/vendor/UnicodeExtra/lakefile.toml`, replace the UnicodeBasic `git`/`rev` require with `path = "../UnicodeBasic"`.
2. Delete `bench/vendor/UnicodeExtra/lake-manifest.json` and `bench/vendor/UnicodeBasic/lake-manifest.json`. The UnicodeExtra one pins UnicodeBasic by git URL and commit.
3. Set each copy's `lean-toolchain` to the library's toolchain, `leanprover/lean4:v4.35.0` at the time of PR #85.
4. Rebuild in `bench/` and commit the regenerated `bench/lake-manifest.json`. Check that every entry has `"type": "path"` and that no entry carries a `url`.
5. Change `theirs_commit=` in `.github/workflows/bench.yml` to the new full commit id. Also change the commit named in `README.md` and in the comment in `bench/lakefile.toml`.

## Why it matters

If one level still names a git source, the build reaches for the network again. The benchmark then fails where no network is available, and that is the case the copies exist for. Treat a manifest entry with a `url` as a sign that one level was missed.

Before PR #85, CI ran `lake update` and then checked that the resolved UnicodeExtra commit started with `44228db53c81`. That check is gone. The workflow now writes `BENCH_THEIRS_COMMIT` from a constant. If someone re-copies UnicodeExtra and leaves the constant alone, every report names the wrong upstream commit and CI stays green. Only the reviewer of the re-copy can catch it, so the constant must change in the same diff as `bench/vendor/`.

## Evidence

- PR #85, `bench/vendor/UnicodeExtra/lakefile.toml`: the UnicodeBasic require changes from `git = "https://github.com/fgdorais/lean4-unicode-basic"`, `rev = "main"` to `path = "../UnicodeBasic"`.
- PR #85 deletes `bench/vendor/UnicodeExtra/lake-manifest.json`, which held a `"type": "git"` entry for UnicodeBasic at `7dcace6ae0fc18882157a2ad6744452e57542987`. It also deletes `bench/vendor/UnicodeBasic/lake-manifest.json`.
- PR #85 adds `bench/lake-manifest.json`. Its three entries are all `"type": "path"`. UnicodeBasic appears with `"inherited": true` and `"dir": "vendor/UnicodeExtra/../UnicodeBasic"`. PR #85 also removes `/bench/lake-manifest.json` from `.gitignore`.
- PR #85, `.github/workflows/bench.yml`: removes the `lake update` step and the `jq`/`grep` check on the resolved commit. Adds `theirs_commit=44228db53c8104753bf02bff36279a65ea46dce4`, with a comment saying it changes only when the copy is re-made, and writes `BENCH_THEIRS_COMMIT=$theirs_commit`.
- PR #85, `bench/Bench/Report.lean`: the `theirsCommit` doc comment now says the copy in `vendor/UnicodeExtra` was taken from that commit.
