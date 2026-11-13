---
module: licensing
date: 2026-11-13
problem_type: convention
component: documentation
severity: low
audience: both
related_components:
  - data
tags:
  - notice
  - unicode-license
  - copyright
  - ucd-data
applies_when:
  - Updating or replacing the Unicode data files under data/ucd/
  - Reviewing a change that adds a new Unicode version directory
---

# Keep the Unicode copyright line in NOTICE in step with the shipped data

## Context

`NOTICE` reproduces the Unicode License V3 that covers the Unicode data the library ships. That copy includes the line `Copyright © <years> Unicode, Inc.`. The data directory carries its own `LICENSE.txt` with the same line. The two copies drifted: `NOTICE` still said `1991-2024` after the shipped data had moved to `1991-2026`. Nothing caught it, because no build step, test or CI check reads `NOTICE`.

## Solution

Treat the `Copyright ©` line in `NOTICE` as part of any Unicode data update. When you add or replace a version under `data/ucd/`, copy that version's `LICENSE.txt` copyright line into `NOTICE` exactly. Find the line by its text, not by line number, since the header above it can change length. A quick check is to grep `^Copyright ©.*Unicode, Inc\.$` in both files and confirm the two outputs are identical.

As a reviewer, ask for this check on any change that touches `data/ucd/`.

## Why it matters

`NOTICE` is the file people read to learn what licence terms they accept when they redistribute the library. A wrong year range there misstates the upstream notice. The data checksums in `SHA256SUMS` protect the data files, not this hand-kept copy. So a data update can pass every check and still leave `NOTICE` wrong.

## Evidence

- PR #26 changes `NOTICE` from `Copyright © 1991-2024 Unicode, Inc.` to `Copyright © 1991-2026 Unicode, Inc.`; the diff touches only `NOTICE` and `README.md`.
- The PR #26 description states that the new `NOTICE` line matches the one in `data/ucd/18.0.0/LICENSE.txt`, and that the two `Copyright` lines were printed and compared as the check.
- Issue 25 reports the mismatch (`NOTICE` 1991-2024 against data 1991-2026) as found by reading, not by any failing check.
- Verification step, not evidence from the change: grep the `Copyright ©` line in `NOTICE` and in the current `data/ucd/*/LICENSE.txt` and compare.
