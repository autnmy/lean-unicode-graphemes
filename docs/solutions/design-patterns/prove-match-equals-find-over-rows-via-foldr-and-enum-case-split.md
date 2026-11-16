---
module: Segmentation.Slice
date: 2026-11-16
problem_type: design_pattern
component: Segmentation
severity: medium
audience: both
related_components:
  - Segmentation.Graphemes
tags:
  - lean
  - proof-technique
  - fast-path
  - breakrows
  - simp
applies_when:
  - A fast `match` must be proved equal to a reference that runs `List.find?` over a list of rule closures.
  - The equality must hold for every state, with no reachable-state hypothesis.
---

# Prove a match equal to a find over rule rows through a foldr form and an enum case split

## Context

`breaksBefore` decides a grapheme boundary with `List.find?` over the twelve rows of `breakRows`. `breaksBeforeFast` makes the same decision with one `match` on the previous and next break class, then three flag tests. The equality `breaksBeforeFast_eq_breaksBefore` must hold for every `ScanState`, with no hypothesis, because a hypothesis would weaken the statement.

`simp` does not compare a `List.find?` result with a `match` well. It also cannot finish if the fast arms read inputs the reference rows do not read.

## Solution

1. Restate the search as a chain of `if`s with a private lemma, proved by induction on the row list:

```lean
private theorem breaksBefore_eq_foldr (s : ScanState) (next : Props) :
    breaksBefore s next =
      breakRows.foldr (fun row rest => if row.applies s next then row.breaks else rest) true
```

The final `true` is the default break (GB999).

2. In the main proof, rewrite with that lemma, destructure the state and the properties, and split only on the two enum fields. Leave the Boolean flags as free variables:

```lean
obtain ⟨⟨prevGcb, _, _⟩, _, _, _, _⟩ := s
obtain ⟨nextGcb, _, _⟩ := next
cases prevGcb <;> cases nextGcb <;>
  simp [breaksBeforeFast, breakRows, gcbIn, incbIs, isExtPict]
```

`simp` then closes each class pair, with the flags still symbolic. No `native_decide` is needed; it would add its own axiom and the keyword scan forbids it. A full `decide` over every state is too large.

3. Make each fast arm read exactly what its reference row reads. The GB12/GB13 row tests `s.riOdd` and the next class only, never `s.prev`. So the fast fallback arm is `s.riOdd && next.gcb == .regionalIndicator`. It does not also require the previous class to be a regional indicator, even though a reachable state with `riOdd` set always has one. An arm that also tested the previous class would agree only on reachable states, and the unconditional equality would fail.

4. Keep the arm order of the rows. The first row that applies decides, so CR LF (GB3) comes before the CR/LF/Control breaks (GB4, GB5), and those come before the Extend and Prepend joins (GB9, GB9b).

## Why it matters

The `foldr` lemma is the step that lets one generic `simp` call close every case. Without it, each case has to unfold `List.find?` by hand. Mirroring the reference inputs is what lets the theorem carry no hypothesis. If an arm copies another library's shape instead, the proof breaks or forces a reachable-state hypothesis, and that weakens the statement.

## Evidence

- PR #93, `Segmentation/Slice.lean`: adds `breaksBefore_eq_foldr` (induction on `rows` with `List.find?_cons` and `List.foldr_cons`), and `breaksBeforeFast_eq_breaksBefore`, proved by the destructure, `cases prevGcb <;> cases nextGcb` and `simp` shown above.
- PR #93, `SegmentationDev/Test/BreaksBeforeFast.lean`: `breaksBeforeFast_gb12_reads_ri_flag_not_previous_class` checks that `riOdd` set with `prev` Other, then a regional indicator, gives `false`. Its comment says a fast arm that also required a regional-indicator previous class would hold only on reachable states.
- The same file checks rule order: `breaksBeforeFast_gb5_before_control_wins_over_gb9b_prepend`, `breaksBeforeFast_control_then_extend_is_a_break` and `breaksBeforeFast_gb3_cr_lf_joins_with_every_flag_set`.
- The same file ends with `#assert_axioms Segmentation.breaksBeforeFast_eq_breaksBefore`, which the PR reports as passing.
