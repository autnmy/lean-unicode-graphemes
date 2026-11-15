---
module: Lean source formatting
date: 2026-11-15
problem_type: convention
component: development_workflow
severity: low
audience: both
related_components:
  - testing_framework
tags:
  - lean
  - whitespace
  - line-wrapping
  - git-diff
applies_when:
  - Checking Lean edits intended to change only spaces and line breaks
---

# Check line wraps with normalized source, not git diff -w

## Context

`git diff -w` still reports a line split into two. It ignores whitespace differences within compared lines, not the line structure itself. Requiring empty output therefore rejects valid line-wrapping edits.

For example, `Segmentation/Statements.lean` wraps the declaration of `props`, `graphemes`, and `boundaries` onto two lines. No identifier changes, but the line split remains visible to that command.

## Solution

Compare the original and edited contents after removing spaces and newlines. Before committing, when `HEAD` still holds the original file, run this command in Bash:

```bash
diff <(git show HEAD:Segmentation/Statements.lean | tr -d ' \n') \
     <(tr -d ' \n' < Segmentation/Statements.lean)
```

Empty output establishes equality under that normalization. Repeat the comparison for each edited Lean file. After committing, use the actual pre-edit revision instead of `HEAD`.

Normalization does not establish equivalent Lean syntax. Removing spaces can hide changed token boundaries, and changing indentation can affect parsing. Review the actual diff and retain the executable checks:

```bash
lake build
lake test
lake env lean SegmentationDev/Test/HeadlineAxioms.lean
```

The last command checks the permitted axioms for the main theorems. These checks complement the text comparison; neither replaces the other.

## Why it matters

An unsuitable diff check rejects the intended formatting change. A normalized comparison alone can accept changes that alter how Lean reads the source. Use both text inspection and Lean checks to cover these distinct risks.

## Evidence

PR #45 wraps lines in `Segmentation/RangeLookup.lean`, `Segmentation/ScanInvariants.lean`, and `Segmentation/Statements.lean`. The declaration in `Segmentation/Statements.lean` changes from one line to two while retaining the binder order.

The pull request's test plan reports that removing spaces and newlines leaves all three edited files identical to their base versions. It also reports successful `lake build`, `lake test` with 15 checks passed, and the main-theorem axiom check. These results support using the normalized comparison together with Lean checks for these formatting edits.
