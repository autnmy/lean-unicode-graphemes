---
module: ci
date: 2026-11-15
problem_type: convention
component: development_workflow
severity: medium
audience: both
related_components:
  - bench
tags:
  - github-actions
  - workflow-triggers
  - pull-request
  - path-filter
applies_when:
  - Adding or editing a workflow that runs only on pushes to main or on manual dispatch
  - Splitting a slow or optional job into its own workflow file
---

# A main-only workflow needs a path-filtered pull_request trigger that names itself

## Context

The Benchmark workflow (`.github/workflows/bench.yml`) is in a file of its own. That way it never slows down the library checks in `ci.yml`. It ran only on `push` to `main` and on `workflow_dispatch`. So the pull request that added it never ran it. Its setup was broken, and the break showed up only on the first run after merge.

## Solution

Add a `pull_request` trigger limited to the paths the workflow covers. Include the workflow file itself, so that a change to the workflow alone also runs it:

```yaml
on:
  push:
    branches: [main]
  pull_request:
    paths:
      - 'bench/**'
      - '.github/workflows/bench.yml'
  workflow_dispatch:
```

Use `pull_request`, not `pull_request_target`. With `pull_request`, code from a fork runs with the workflow's read-only token and without secrets. That matters here because the job compiles third-party code (since PR #85, the copies in `bench/vendor/`; before that, code fetched from another repository). Keep the workflow in its own file, and do not refer to it from `ci.yml`. Pull requests that touch neither path then skip it, and the main checks never wait for it.

Branch protection decides whether a check is required, and that setting lives outside the repository. A trigger cannot make a check optional. Say in the pull request that the check is meant to stay optional.

## Why it matters

If a workflow does not run on pull requests, a green pull request tells you nothing about it. The path filter keeps the cost limited to pull requests that can break the workflow. Listing the workflow file in the filter covers the most common way to break it, which is editing the workflow itself.

## Evidence

- PR #62 adds the `pull_request` trigger with exactly `bench/**` and `.github/workflows/bench.yml` to `.github/workflows/bench.yml`. It rewrites the header comment to say that pull requests use `pull_request` and never `pull_request_target`.
- Issue #57 records why the break landed unseen: the workflow ran only on pushes to `main` and on manual dispatch.
- `README.md` in the same pull request says that pull requests touching neither path do not run the workflow. It also says the workflow is an optional check in a workflow of its own.
- The note on the pull request points out that required checks are set in branch protection outside the repository.
