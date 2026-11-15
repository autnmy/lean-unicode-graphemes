---
module: docs/solutions
date: 2026-11-13
problem_type: convention
component: documentation
severity: low
audience: both
related_components:
  - SegmentationDev.Test
tags:
  - learnings
  - evidence
  - file-deletion
  - stale-references
applies_when:
  - A change deletes, renames or merges files
  - A docs/solutions learning names one of those files in its Evidence section
---

# Repoint a learning's evidence when you delete a file it cites

## Context

Each learning under `docs/solutions/` has an Evidence section, and that section names files a reader can open to check the claim. A change that deletes or merges one of those files leaves the learning pointing at a path that no longer exists. The claim may still be true, but no one can check it anymore.

The change that adds the deletion can look unrelated to the docs, for example a change that only moves tests. In review of PR #29, this edit was called out of scope. The author kept it, because the deletion is what breaks the reference.

## Solution

When a change deletes or renames a file, search `docs/solutions/` for its path. In the same change, point each matching Evidence line at the file that now holds the cited content. Before you do, read the new file and confirm it still says what the learning claims. If nothing holds that content anymore, say so in the learning rather than leaving a dead path.

## Why it matters

A learning whose evidence cannot be opened reads as unverified, and a later check of the docs against the tree will flag it or drop it. Fixing the path in the same change costs one line. Fixing it later means someone has to find out which deleted file the claim came from.

## Evidence

- PR #29 deletes `SegmentationTest/AxiomCheckerDisallowed.lean` and `SegmentationTest/DisallowedAxiomsReduceBoolAndUser.lean`.
- In the same pull request, `docs/solutions/conventions/native-decide-adds-its-own-axiom-not-ofreducebool.md` changes its Evidence line from those two paths to `SegmentationTest/DisallowedAxioms.lean`.
- `SegmentationTest/DisallowedAxioms.lean`, added by PR #29 and now at `SegmentationDev/Test/DisallowedAxioms.lean`, keeps the comment that `Lean.ofReduceBool` stands for any other axiom outside the allowed three, which is the claim the learning cites.
