---
module: Segmentation
date: 2026-11-15
problem_type: convention
component: proofs
severity: low
audience: both
related_components:
  - Segmentation/Cuts.lean
  - Segmentation/ScanInvariants.lean
  - Segmentation/RangeLookup.lean
tags:
  - simp
  - simp-only
  - proof-style
  - omega
applies_when:
  - Writing or reviewing a proof step where `simp` runs before another tactic such as `omega`
  - Someone proposes to squeeze a `simp` that already closes its goal
---

# Squeeze non-terminal `simp` calls; leave terminal `simp` calls bare

## Context

A terminal `simp` closes its goal by itself, as in `by simp`. A non-terminal `simp` only rewrites the goal and leaves it for a later tactic, as in `by simp; omega`. The two fail in different ways when the default simp lemma set changes. A terminal call either still closes the goal or fails right there, at that line. A non-terminal call can leave the goal in a different shape, and then the later tactic fails with an error that does not point at `simp`.

The proofs in `Segmentation/` now follow one rule for this. Both kinds of call appear in the same proofs, so the code alone does not tell you that the split is on purpose.

## Solution

- When `simp` runs before another tactic, write `simp only [...]`. Use the lemma list that `simp?` reports at that site. This covers `simp; omega`, `simp at h; omega` and `<;> simp <;> omega`.
- When `simp` closes its goal alone (`by simp`, `by simp [hz]`, `simp at hlen` that closes a contradiction), leave it bare. Do not squeeze it.
- When one `simp` runs after a case split such as `cases odd <;> simp <;> omega`, a single `simp only` list must work in every branch. Run `simp?` in each branch and join the lists. In `parity_snoc` the list carries both `Bool.not_false` and `Bool.not_true`, one for each `Bool` case.
- `simpa ... using h` was not part of this rule and was left as it was.

## Why it matters

An explicit lemma list pins the shape of the goal that `omega` receives. A later change to the default simp set then cannot quietly break the step after it. A terminal call gains nothing from that pin: it fails at its own line if it fails at all. Squeezing it only adds a long list that goes stale. The style guide cited in the issue says the same: terminal `simp` calls should not be squeezed. A reviewer who sees a bare terminal `simp` should not ask for it to be squeezed. A reviewer who sees a new `simp; omega` should ask for `simp only`.

## Evidence

- PR #61 (closes issue #52) replaces ten non-terminal bare `simp` calls with `simp only [...]`. The sites are in `Segmentation/Cuts.lean` (`cutInside_cons`, `mem_scanl_go`), `Segmentation/ScanInvariants.lean` (`matches_pairs_of_all`, `Pat.matches_pairs_iff`, `parity_snoc`, `Pat.matches_pairs_one_iff`) and `Segmentation/RangeLookup.lean` (`Range.scanList_eq_default`).
- The diff keeps terminal calls bare next to the squeezed ones. Examples are `hall x (by simp)` in `matches_pairs_of_all`, `exact ⟨0, by simp, by simp, by simpa using hb⟩` in `cutInside_cons`, and `· simp at hlen` in `Pat.matches_pairs_one_iff`.
- In `Segmentation/ScanInvariants.lean`, `parity_snoc` changes from `cases odd <;> simp <;> omega` to one `simp only` list that holds `Bool.not_false` and `Bool.not_true`.
- Issue #52 states the rule and its source, the style guide at mathlib.org/contribute/style.html: terminal simp calls should not be squeezed, and non-terminal ones should be, so that a change to the simp set cannot break the proof. The issue also says to leave the four terminal calls that issue #41 asks to squeeze.
