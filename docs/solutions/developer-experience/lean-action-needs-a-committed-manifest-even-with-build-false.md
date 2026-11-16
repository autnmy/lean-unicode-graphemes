---
module: bench
date: 2026-11-15
problem_type: developer_experience
component: development_workflow
severity: medium
audience: both
related_components:
  - ci
  - bench
tags:
  - lean-action
  - elan
  - lake-manifest
  - github-actions
  - toolchain
applies_when:
  - A workflow points `leanprover/lean-action` at a Lake package whose `lake-manifest.json` is not committed
  - A sub-package pins a different toolchain from the root package
---

# lean-action needs a committed manifest, even with build: false

## Context

The Benchmark workflow measures the `bench/` package. When this was written, that package did not commit `bench/lake-manifest.json`, the file that locks dependency versions. Instead, `lake update` wrote the file fresh on every run. The workflow used `leanprover/lean-action` v1.6.2 with `lake-package-directory: bench`, `build: false` and `test: false`. The goal was for the action to install the toolchain and nothing more.

Even with those settings, the action still runs its configure step. That step exits with `No lake-manifest.json found. Run lake update to generate manifest`. It exits before any later step can run `lake update`, so every run failed during setup. Neither library was measured.

Current state: since PR #85, `bench/` requires UnicodeExtra and UnicodeBasic by path from `bench/vendor/`, commits `bench/lake-manifest.json`, runs no `lake update`, and uses the library's own toolchain, `leanprover/lean4:v4.35.0`. The workflow still points `lean-action` at the root and keeps the toolchain install and version check below. The rejected option and the v4.36.0-rc2 toolchain below are history.

## Solution

Point the action at a package that has a committed manifest, which here is the repository root. Use it only to put `elan`, the Lean toolchain manager, on the PATH. Then install the sub-package's toolchain in its own directory, and fail unless `lean` reports that version:

```sh
toolchain=$(cat lean-toolchain)
elan toolchain install "$toolchain"
version=$(lean --version)
expected="version ${toolchain#leanprover/lean4:v},"
case "$version" in
  *"$expected"*) ;;
  *) echo "Expected lean to report $expected from $toolchain; got: $version" >&2; exit 1 ;;
esac
```

The version check matters because the action installs the root toolchain (v4.35.0). The bench pins a different one (`leanprover/lean4:v4.36.0-rc2`). Without the check, results could carry a toolchain label that never ran.

The change considered and rejected two other options:

- **Commit `bench/lake-manifest.json`.** That file is meant to be written by `lake update`. Committing it also gives a pull request a second place to change the pinned dependency.
- **Use a custom elan installer.** That is one more installer to pin by commit, a job `lean-action` already does.

The cost of this option is a second toolchain download in each run.

## Why it matters

If you point `lean-action` at a package that writes its manifest at run time, setup always fails. The failure says nothing about the code under test. The settings `build: false` and `test: false` do not skip the manifest check. If you mix toolchains on purpose, check `lean --version` explicitly. Otherwise a mismatch passes without anyone noticing.

## Evidence

- PR #62 changes `.github/workflows/bench.yml`. It drops `lake-package-directory: bench` from the `leanprover/lean-action` step and adds the step "Install and check the bench toolchain" shown above.
- Issue #57 quotes the earlier failure: `##[error]No lake-manifest.json found. Run lake update to generate manifest`, from run 43699923576 on `main`.
- In the CI log for this pull request's Benchmark run, setup passed. The run then failed at the later "Fetch UnicodeExtra" (`lake update`) step, so the setup failure is gone.
- `README.md` in the same pull request lists the `elan toolchain install "$(cat lean-toolchain)"` step before `lake update`.
