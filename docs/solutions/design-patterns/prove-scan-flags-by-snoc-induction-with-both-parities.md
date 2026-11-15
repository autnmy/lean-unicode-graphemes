---
module: Segmentation
date: 2026-11-12
problem_type: design_pattern
component: proofs
severity: medium
audience: both
related_components:
  - Segmentation/Graphemes.lean
  - Segmentation/Statements.lean
tags:
  - scan-state
  - induction
  - invariants
  - regional-indicator
applies_when:
  - Proving that a ScanState flag equals a rule's left-side pattern
  - Adding a new flag to ScanState.push
---

# Prove scan flags by adding code points at the end, and prove flipping flags for both values

## Context

`ScanState.push` reads a text one code point at a time, adding each new code point at the end. A rule's left side in `Segmentation/Statements.lean` is a pattern over the whole text before a position. To prove that a flag equals its pattern, the proof must follow the same order the scan reads in. Plain list induction in Lean adds elements at the front, so it does not match `foldl ScanState.push`.

The parity flag `riOdd` is harder still. It says whether the run of regional indicators (RI) at the end of the text has odd length. `push` computes the new value by flipping the old one. So the induction step for `riOdd = true` needs the induction hypothesis for `riOdd = false`, and the reverse.

## Solution

- Rewrite the fold so that the last step is one `push`. The change uses `foldl_push_snoc`: `(l ++ [q]).foldl push s = (l.foldl push s).push q`.
- Do induction by adding one element at the end (the change's private `snoc_induction`, proved by reversing the list).
- For each pattern, first prove a "snoc" lemma. It says what the left side means for `l ++ [q]` in terms of `l` and `q`. One example is `Left.holds_ending_one_star_snoc`: the run is extended when `q` is in `e`, and a new run starts when `q` is in `a`. For `linkerTail` and `pictTail`, the step is `rw` with this lemma and the induction hypothesis, then `simp [ScanState.push]`. `zwjAfterPict` closes the same way after it also rewrites with `foldl_push_pictTail`. The `riOdd` step needs more: `simp only` with both halves of the hypothesis, then a `cases` split on `gcbIn [.regionalIndicator] q` and on the previous `riOdd`.
- A flag that reads another flag gets its hypothesis from that flag's lemma, not from its own. `zwjAfterPict` rewrites with `foldl_push_pictTail`.
- For a flag that flips, state the invariant as a conjunction of both values. `foldl_push_riOdd` proves `(riOdd = true ↔ RunParity c true l) ∧ (riOdd = false ↔ RunParity c false l)`. Then take `.1` for the public lemma. Name the parity as a definition (`RunParity`) that has its own `snoc` and `nil` lemmas.
- Start the fold from a blank state with every flag false (`blankState`), so the empty list is the base case. `ScanState.start p` is then just the first `push`.

## Why it matters

If you induct from the front, you have to reason about a whole pattern match on `x :: l` against a fold whose last step is unknown. That proof does not close cleanly. If you state only `riOdd = true`, the induction step does not go through, because the previous state could have `riOdd = false`. Use the same pattern for any new `ScanState` flag. It makes each flag its own theorem, so a wrong update in `push` fails at that flag's lemma.

## Evidence

PR #21 adds `Segmentation/ScanInvariants.lean`, which contains `foldl_push_snoc`, `snoc_induction`, `blankState` and `scanStateOf_eq_foldl`. It also adds the snoc lemmas `Left.holds_ending_one_star_snoc`, `Left.holds_ending_one_star_one_snoc` and `RunParity.snoc`. The doc comment on `foldl_push_riOdd` states that `riOdd` tracks both parities at once because `push` reads the previous parity to flip it. Its proof uses `ih.1` and `ih.2` together. `foldl_push_zwjAfterPict` rewrites with `foldl_push_pictTail` instead of its own hypothesis. `lake build` and `lake test` pass on this change.
