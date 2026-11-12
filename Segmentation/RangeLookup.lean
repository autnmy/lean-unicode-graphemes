import Segmentation.Tables.Range

/-!
# The binary search agrees with a linear scan

`Range.lookup` finds a code point's range by binary search, which is only right when the
table is sorted and its ranges do not overlap. This module states that condition as
`Range.Sorted` and proves `Range.lookup_eq_scan`: on a sorted table the binary search gives
the same value as `Range.scan`, a plain scan that takes the first range holding the code point.

`Range.Sorted` is a `Bool` check, `Range.chainOK`, on the table's ranges, so `decide` can
evaluate it on a concrete table in the kernel. It asks that every range has `lo ≤ hi` and that
each range ends before the next one starts. Together these give `hi < lo` for every pair of
ranges in order, not only neighbours, so at most one range holds any code point, every range
left of a range that starts after `n` also misses `n`, and the same on the right.

The proof follows the search window. While the window `[start, stop)` holds every range that
holds `n`, each step keeps that true, and the window shrinks by at least one each step. The
search starts with `table.size + 1` steps for a window of `table.size` ranges, so it never runs
out of steps while the window is non-empty.
-/

namespace Segmentation.Tables

/--
The value of the first range in `ranges` that holds code point `n`, or `default` when none
holds it. This is the plain search `Range.lookup` is proved against, so it does not use it.
-/
def Range.scanList {α : Type} (default : α) : List (Range α) → Nat → α
  | [], _ => default
  | range :: rest, n => if range.lo ≤ n ∧ n ≤ range.hi then range.value else scanList default rest n

/-- The value of the first range in `table` that holds code point `n`, or `default`. -/
def Range.scan {α : Type} (default : α) (table : Array (Range α)) (n : Nat) : α :=
  Range.scanList default table.toList n

/--
Whether every range in `ranges` has `lo ≤ hi` and ends before the next one starts. The check
on each range is needed as well as the one on neighbours: a middle range with `lo > hi` could
otherwise sit between two ranges that overlap each other.
-/
def Range.chainOK {α : Type} : List (Range α) → Bool
  | [] => true
  | [range] => decide (range.lo ≤ range.hi)
  | range :: next :: rest =>
    decide (range.lo ≤ range.hi) && decide (range.hi < next.lo) && chainOK (next :: rest)

/-- `table` is sorted by `lo` with no overlapping ranges, as `Range.lookup` needs. -/
def Range.Sorted {α : Type} (table : Array (Range α)) : Prop :=
  Range.chainOK table.toList = true

instance {α : Type} (table : Array (Range α)) : Decidable (Range.Sorted table) :=
  inferInstanceAs (Decidable (Range.chainOK table.toList = true))

/-- Every range in a list that passes `chainOK` has `lo ≤ hi`. -/
theorem Range.chainOK_lo_le_hi {α : Type} :
    ∀ (ranges : List (Range α)), Range.chainOK ranges = true →
      ∀ (i : Nat) (hi : i < ranges.length), ranges[i].lo ≤ ranges[i].hi
  | [], _, i, hi => absurd hi (by simp)
  | [range], h, i, hi => by
    simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    simpa [Range.chainOK] using h
  | range :: next :: rest, h, i, hi => by
    simp only [Range.chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => exact h.1.1
    | succ i =>
      exact Range.chainOK_lo_le_hi (next :: rest) h.2 i (by simpa using hi)

/-- In a list that passes `chainOK`, every range ends before any later range starts. -/
theorem Range.chainOK_hi_lt_lo {α : Type} :
    ∀ (ranges : List (Range α)), Range.chainOK ranges = true →
      ∀ (i j : Nat) (hij : i < j) (hj : j < ranges.length),
        ranges[i].hi < ranges[j].lo
  | [], _, _, _, _, hj => absurd hj (by simp)
  | [_], _, i, j, hij, hj => by simp only [List.length_singleton] at hj; omega
  | range :: next :: rest, h, i, j, hij, hj => by
    have hchain := h
    simp only [Range.chainOK, Bool.and_eq_true, decide_eq_true_eq] at hchain
    obtain ⟨⟨_, hfirst⟩, hrest⟩ := hchain
    cases i with
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        exact Range.chainOK_hi_lt_lo (next :: rest) hrest i j (by omega) (by simpa using hj)
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        cases j with
        | zero => simpa using hfirst
        | succ j =>
          have hnext := Range.chainOK_lo_le_hi (next :: rest) hrest 0 (by simp)
          have hlater := Range.chainOK_hi_lt_lo (next :: rest) hrest 0 (j + 1) (by omega)
            (by simpa using hj)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hnext hlater ⊢
          omega

/-- `scanList` gives `default` when no range in the list holds `n`. -/
theorem Range.scanList_eq_default {α : Type} (default : α) (n : Nat) :
    ∀ (ranges : List (Range α)),
      (∀ (i : Nat) (hi : i < ranges.length), ¬ (ranges[i].lo ≤ n ∧ n ≤ ranges[i].hi)) →
        Range.scanList default ranges n = default
  | [], _ => rfl
  | range :: rest, hnone => by
    have hhead := hnone 0 (by simp)
    simp only [List.getElem_cons_zero] at hhead
    simp only [Range.scanList, hhead, ite_false]
    exact Range.scanList_eq_default default n rest
      (fun i hi => by
        have hlater := hnone (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at hlater
        exact hlater)

/-- `scanList` gives the value of range `i` when range `i` holds `n` and no earlier range does. -/
theorem Range.scanList_eq_value {α : Type} (default : α) (n : Nat) :
    ∀ (ranges : List (Range α)) (i : Nat) (hi : i < ranges.length),
      ranges[i].lo ≤ n ∧ n ≤ ranges[i].hi →
      (∀ (j : Nat) (hj : j < i), ¬ (ranges[j].lo ≤ n ∧ n ≤ ranges[j].hi)) →
        Range.scanList default ranges n = ranges[i].value
  | [], _, hi, _, _ => absurd hi (by simp)
  | range :: rest, 0, _, hhold, _ => by
    simp only [List.getElem_cons_zero] at hhold
    simp [Range.scanList, hhold]
  | range :: rest, i + 1, hi, hhold, hearlier => by
    have hhead := hearlier 0 (by omega)
    simp only [List.getElem_cons_zero] at hhead
    simp only [Range.scanList, hhead, ite_false, List.getElem_cons_succ]
    exact Range.scanList_eq_value default n rest i (by simpa using hi) (by simpa using hhold)
      (fun j hj => by simpa using hearlier (j + 1) (by omega))

/-- On a sorted table, `scan` gives `default` when no range holds `n`. -/
theorem Range.scan_eq_default {α : Type} (default : α) (table : Array (Range α)) (n : Nat)
    (hnone : ∀ (i : Nat) (hi : i < table.size), ¬ (table[i].lo ≤ n ∧ n ≤ table[i].hi)) :
    Range.scan default table n = default :=
  Range.scanList_eq_default default n table.toList
    (fun i hi => by simpa using hnone i (by simpa using hi))

/-- On a sorted table, `scan` gives the value of the one range that holds `n`. -/
theorem Range.scan_eq_value {α : Type} (default : α) {table : Array (Range α)}
    (hsorted : Range.Sorted table) (n i : Nat) (hi : i < table.size)
    (hhold : table[i].lo ≤ n ∧ n ≤ table[i].hi) :
    Range.scan default table n = table[i].value := by
  have hpairs := Range.chainOK_hi_lt_lo table.toList hsorted
  have heq := Range.scanList_eq_value default n table.toList i (by simpa using hi)
    (by simpa using hhold)
    (fun j hj hjhold => by
      have hlt := hpairs j i hj (by simpa using hi)
      simp only [Array.getElem_toList] at hlt hjhold
      omega)
  simpa [Range.scan] using heq

/--
The search keeps every range that holds `n` inside its window `[start, stop)`, and has at
least as many steps left as ranges in the window, so it ends at the range `scan` finds.
-/
theorem Range.lookup_search_eq_scan {α : Type} (default : α) {table : Array (Range α)}
    (hsorted : Range.Sorted table) (n : Nat) :
    ∀ (steps start stop : Nat), stop ≤ table.size → stop - start ≤ steps →
      (∀ (i : Nat) (hi : i < table.size), (i < start ∨ stop ≤ i) →
        ¬ (table[i].lo ≤ n ∧ n ≤ table[i].hi)) →
        Range.lookup.search default table n steps start stop = Range.scan default table n
  | 0, start, stop, _, hsteps, houtside => by
    simp only [Range.lookup.search]
    exact (Range.scan_eq_default default table n
      (fun i hi => houtside i hi (by omega))).symm
  | steps + 1, start, stop, hstop, hsteps, houtside => by
    have hpairs := Range.chainOK_hi_lt_lo table.toList hsorted
    have hlohi := Range.chainOK_lo_le_hi table.toList hsorted
    simp only [Array.getElem_toList, Array.length_toList] at hpairs hlohi
    simp only [Range.lookup.search]
    split
    · rename_i hwindow
      have hmid : (start + stop) / 2 < table.size := by omega
      rw [Array.getElem?_eq_getElem hmid]
      dsimp only
      split
      · rename_i hleft
        apply Range.lookup_search_eq_scan default hsorted n steps start ((start + stop) / 2)
          (by omega) (by omega)
        intro i hi hside
        rcases hside with hside | hside
        · exact houtside i hi (Or.inl hside)
        · rcases Nat.lt_or_ge i stop with hin | hout
          · -- Ranges from the middle on start at or after the middle range, so after `n`.
            rcases Nat.eq_or_lt_of_le hside with hsame | hlater
            · subst hsame; omega
            · have := hpairs _ i hlater hi
              have := hlohi _ hmid
              omega
          · exact houtside i hi (Or.inr hout)
      · rename_i hleft
        split
        · rename_i hright
          apply Range.lookup_search_eq_scan default hsorted n steps ((start + stop) / 2 + 1) stop
            hstop (by omega)
          intro i hi hside
          rcases hside with hside | hside
          · rcases Nat.lt_or_ge i start with hout | hin
            · exact houtside i hi (Or.inl hout)
            · -- Ranges up to the middle end at or before the middle range, so before `n`.
              rcases Nat.lt_or_ge i ((start + stop) / 2) with hearlier | hsame
              · have := hpairs i _ hearlier hmid
                have := hlohi _ hmid
                omega
              · have : i = (start + stop) / 2 := by omega
                subst this; omega
          · exact houtside i hi (Or.inr hside)
        · rename_i hright
          exact (Range.scan_eq_value default hsorted n _ hmid (by omega)).symm
    · exact (Range.scan_eq_default default table n
        (fun i hi => houtside i hi (by omega))).symm

/-- On a sorted table, the binary search `Range.lookup` gives the same value as `Range.scan`
for every code point `n`. -/
theorem Range.lookup_eq_scan {α : Type} {default : α} {table : Array (Range α)}
    (h : Range.Sorted table) (n : Nat) :
    Range.lookup default table n = Range.scan default table n :=
  Range.lookup_search_eq_scan default h n (table.size + 1) 0 table.size
    (Nat.le_refl _) (by omega) (fun i hi hside => by omega)

end Segmentation.Tables
