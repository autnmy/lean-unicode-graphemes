---
module: bench
date: 2026-11-15
problem_type: convention
component: lakefile
severity: medium
audience: both
related_components:
  - ci
  - benchmark
tags:
  - lake
  - lakefile
  - git
  - pinning
  - rev
  - lake-update
applies_when:
  - A lakefile `[[require]]` entry pins a git dependency to a commit with `rev`
  - "`lake update` fails with `fatal: couldn't find remote ref` followed by a short hex string"
---

# Write a Lake git `rev` as the full 40-digit commit id

## Context

The benchmark lakefile, `bench/lakefile.toml`, pins the UnicodeExtra dependency to one commit, so the code CI builds cannot change under the benchmark. It named that commit by a 12-digit prefix, `rev = "44228db53c81"`.

`lake update` then failed in CI. It printed `fetching revision '44228db53c81'` and then `fatal: couldn't find remote ref 44228db53c81`.

The cause is how Lake gets a pinned commit. It runs `git fetch` against the remote with the `rev` value as the thing to fetch. Issue #63 and the comment PR #66 adds to bench/lakefile.toml give the reason: a git remote serves only refs and full object ids, so fetching an abbreviated id finds nothing. This change does not test that git behaviour itself; the fetch error in issue #63 is consistent with it.

Cloning the dependency in advance does not fix this. Lake skips the fetch and uses a commit that is already present only when `rev` is a full SHA-1 id.

This is history for the benchmark: since PR #85, `bench/lakefile.toml` requires a copy of UnicodeExtra by path from `bench/vendor/`, CI runs no `lake update`, and the prefix check on the resolved commit is gone. The rule still applies to any git require with a `rev`.

## Solution

Write every commit pin in a lakefile `[[require]]` as the full 40-digit id:

```toml
[[require]]
name = "UnicodeExtra"
git = "https://github.com/fgdorais/lean4-unicode-extra"
rev = "44228db53c8104753bf02bff36279a65ea46dce4"
```

Get the full id with `git rev-parse <prefix>` in a clone of the dependency, or from the host's commit page.

A short prefix can still appear in prose, such as a README, because people read it there and Lake does not. If CI checks the resolved commit against a prefix, that check keeps working: a full id still starts with the prefix.

## Why it matters

A short prefix looks like a valid pin. It works with `git checkout` in a local clone, so a reviewer has no reason to doubt it. The failure shows up only when `lake update` reaches the network, and the error message does not say the id is too short.

The obvious workaround, cloning the dependency before `lake update`, also fails, for the same reason. Without this rule, the next person may spend time on fetch settings or caching before finding that the fix is the length of one string.

## Evidence

- PR #66 changes `bench/lakefile.toml` from `rev = "44228db53c81"` to `rev = "44228db53c8104753bf02bff36279a65ea46dce4"`. The comment it adds above the entry gives the reason: Lake passes the id to `git fetch`, and a git remote serves only refs and full object ids, never an abbreviated one.
- Issue #63, which PR #66 closes, records the failing `lake update` output: `fetching revision '44228db53c81'` followed by `fatal: couldn't find remote ref 44228db53c81`. It also reports that, in Lake's source, the shortcut that reuses a commit already present applies only when `rev.isFullSha1`.
- PR #66 also updates the comment in `.github/workflows/bench.yml`. It now says the lakefile names the full id, and that the pin check ties it to the `44228db53c81` prefix the README cites. So the prefix check and the full-id pin work together.
- After PR #66 opened, no check failed at its head commit, including the Benchmark run that had failed at `lake update`.
