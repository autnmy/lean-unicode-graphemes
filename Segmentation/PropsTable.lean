import Segmentation.TableLookup

/-!
# One table for all three properties

`props` reads a code point's three properties with three binary searches, one in each
generated table. This module merges the three tables into `propsRanges`, one sorted table whose
ranges each carry a whole `Props`, so `propsLookup` needs one binary search instead of three.

The merge is computed in Lean from the generated tables rather than generated as a fourth
file, so the generator and its drift check stay as they are. It is proved right for any two
sorted range lists, not only for these tables: `Range.chainOK_mergeWith` says the result is
sorted, and `Range.scanList_mergeWith` says a scan of the result gives, at every code point,
the pair of the two inputs' scans. A check of every code point in the kernel would be far too
slow, which is why the proof goes through these general facts. `propsLookup_eq_props` then
follows from them and the facts in `Segmentation.TableLookup`.

The merge counts its steps, like `Range.lookup`, so its recursion is structural and the kernel
can evaluate it on concrete lists.
-/

namespace Segmentation.Tables

/-- `omega`, after reading the fields of range literals such as `{ lo := y.lo, .. }.lo`, which
`omega` would otherwise treat as unknown numbers. -/
local macro "range_omega" : tactic => `(tactic| ((try dsimp only); omega))

/-- The range `range` with `g` applied to its value. -/
def Range.mapValue {α β : Type} (g : α → β) (range : Range α) : Range β :=
  { lo := range.lo, hi := range.hi, value := g range.value }

/--
Merges two lists of ranges, taking at most `steps` merge steps, into one list whose ranges
carry `f` of both lists' values. A code point only one list covers carries `f` of that list's
value and the other list's default.

Each step looks at the two head ranges. The one that starts first is emitted up to where the
other starts; when both start together, their common part is emitted. What is left of a head
range stays at the front of its list. `Range.mergeWith` gives enough steps.
-/
def Range.mergeSteps {α β γ : Type} (f : α → β → γ) (da : α) (db : β) :
    Nat → List (Range α) → List (Range β) → List (Range γ)
  | 0, _, _ => []
  | _ + 1, [], b => b.map (Range.mapValue (f da))
  | _ + 1, x :: a, [] => (x :: a).map (Range.mapValue (f · db))
  | steps + 1, x :: a, y :: b =>
    if x.lo < y.lo then
      if x.hi < y.lo then
        { lo := x.lo, hi := x.hi, value := f x.value db } :: mergeSteps f da db steps a (y :: b)
      else
        { lo := x.lo, hi := y.lo - 1, value := f x.value db } ::
          mergeSteps f da db steps ({ lo := y.lo, hi := x.hi, value := x.value } :: a) (y :: b)
    else if y.lo < x.lo then
      if y.hi < x.lo then
        { lo := y.lo, hi := y.hi, value := f da y.value } :: mergeSteps f da db steps (x :: a) b
      else
        { lo := y.lo, hi := x.lo - 1, value := f da y.value } ::
          mergeSteps f da db steps (x :: a) ({ lo := x.lo, hi := y.hi, value := y.value } :: b)
    else if x.hi < y.hi then
      { lo := x.lo, hi := x.hi, value := f x.value y.value } ::
        mergeSteps f da db steps a ({ lo := x.hi + 1, hi := y.hi, value := y.value } :: b)
    else if y.hi < x.hi then
      { lo := x.lo, hi := y.hi, value := f x.value y.value } ::
        mergeSteps f da db steps ({ lo := y.hi + 1, hi := x.hi, value := x.value } :: a) b
    else
      { lo := x.lo, hi := x.hi, value := f x.value y.value } :: mergeSteps f da db steps a b

/--
Merges two sorted lists of ranges into one sorted list whose ranges carry `f` of both lists'
values, taking `da` or `db` where one list has no range. A code point neither list covers is
left out, so a scan of the result with default `f da db` reads it as both defaults.
-/
def Range.mergeWith {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
    (a : List (Range α)) (b : List (Range β)) : List (Range γ) :=
  -- Each step drops a range or leaves both heads starting together, and the step after that
  -- drops a range, so two steps per range are enough.
  Range.mergeSteps f da db (2 * (a.length + b.length)) a b

/-! ### The step budget is enough -/

/-- A step budget `Range.mergeSteps` never runs out of on lists `a` and `b`: one merge step
lowers it by at least one. -/
private def Range.mergeBudget {α β : Type} : List (Range α) → List (Range β) → Nat
  | x :: a, y :: b => if x.lo = y.lo then 2 * (a.length + b.length) + 3
    else 2 * (a.length + b.length) + 4
  | a, b => 2 * (a.length + b.length)

private theorem Range.mergeBudget_le {α β : Type} (a : List (Range α)) (b : List (Range β)) :
    Range.mergeBudget a b ≤ 2 * (a.length + b.length) := by
  unfold Range.mergeBudget
  split
  · simp only [List.length_cons]; split <;> omega
  · omega

private theorem Range.mergeBudget_cons {α β : Type} (x : Range α) (a : List (Range α))
    (y : Range β) (b : List (Range β)) :
    2 * (a.length + b.length) + 3 ≤ Range.mergeBudget (x :: a) (y :: b) := by
  simp only [Range.mergeBudget]; split <;> omega

/-! ### Facts about sorted lists -/

/-- Every range in `ranges` starts at `m` or later. -/
private def Range.StartsFrom {α : Type} (m : Nat) (ranges : List (Range α)) : Prop :=
  ∀ range ∈ ranges, m ≤ range.lo

private theorem Range.startsFrom_cons {α : Type} {m : Nat} {range : Range α}
    {ranges : List (Range α)} :
    Range.StartsFrom m (range :: ranges) ↔ m ≤ range.lo ∧ Range.StartsFrom m ranges := by
  simp [Range.StartsFrom]

private theorem Range.startsFrom_mono {α : Type} {m m' : Nat} {ranges : List (Range α)}
    (hle : m' ≤ m) (h : Range.StartsFrom m ranges) : Range.StartsFrom m' ranges :=
  fun range hmem => Nat.le_trans hle (h range hmem)

private theorem Range.chainOK_cons_lo_le_hi {α : Type} {range : Range α}
    {ranges : List (Range α)} (h : Range.chainOK (range :: ranges) = true) :
    range.lo ≤ range.hi := by
  cases ranges with
  | nil => simpa [Range.chainOK] using h
  | cons _ _ =>
    simp only [Range.chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1

private theorem Range.chainOK_of_cons {α : Type} {range : Range α} {ranges : List (Range α)}
    (h : Range.chainOK (range :: ranges) = true) : Range.chainOK ranges = true := by
  cases ranges with
  | nil => rfl
  | cons _ _ =>
    simp only [Range.chainOK, Bool.and_eq_true] at h
    exact h.2

/-- In a list that passes `chainOK`, the ranges after the first start after it ends. -/
private theorem Range.chainOK_cons_startsFrom {α : Type} :
    ∀ (range : Range α) (ranges : List (Range α)), Range.chainOK (range :: ranges) = true →
      Range.StartsFrom (range.hi + 1) ranges
  | _, [], _ => fun _ hmem => absurd hmem (by simp)
  | range, next :: rest, h => by
    have hnext := Range.chainOK_cons_startsFrom next rest (Range.chainOK_of_cons h)
    have hnextlo := Range.chainOK_cons_lo_le_hi (Range.chainOK_of_cons h)
    simp only [Range.chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [Range.startsFrom_cons]
    exact ⟨by omega, Range.startsFrom_mono (by omega) hnext⟩

/-- A range with `lo ≤ hi`, in front of a sorted list that starts after it ends, passes
`chainOK`. -/
private theorem Range.chainOK_cons {α : Type} {range : Range α} {ranges : List (Range α)}
    (hrange : range.lo ≤ range.hi) (hafter : Range.StartsFrom (range.hi + 1) ranges)
    (hranges : Range.chainOK ranges = true) : Range.chainOK (range :: ranges) = true := by
  cases ranges with
  | nil => simpa [Range.chainOK] using hrange
  | cons next rest =>
    have hnext := (Range.startsFrom_cons.mp hafter).1
    simp only [Range.chainOK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hrange, by omega⟩, hranges⟩

/-- Moving the start of a list's first range up to `lo`, still at most its end, keeps the list
passing `chainOK`. -/
private theorem Range.chainOK_trim {α : Type} {range : Range α} {ranges : List (Range α)}
    (lo : Nat) (hlo : lo ≤ range.hi) (h : Range.chainOK (range :: ranges) = true) :
    Range.chainOK ({ lo := lo, hi := range.hi, value := range.value } :: ranges) = true :=
  Range.chainOK_cons hlo (Range.chainOK_cons_startsFrom range ranges h) (Range.chainOK_of_cons h)

private theorem Range.chainOK_map_mapValue {α β : Type} (g : α → β) :
    ∀ (ranges : List (Range α)),
      Range.chainOK (ranges.map (Range.mapValue g)) = Range.chainOK ranges
  | [] => rfl
  | [_] => rfl
  | range :: next :: rest => by
    have := Range.chainOK_map_mapValue g (next :: rest)
    simp only [List.map_cons] at this ⊢
    simp only [Range.chainOK, Range.mapValue] at this ⊢
    rw [this]
    rfl

private theorem Range.startsFrom_map_mapValue {α β : Type} (g : α → β) {m : Nat}
    {ranges : List (Range α)} (h : Range.StartsFrom m ranges) :
    Range.StartsFrom m (ranges.map (Range.mapValue g)) := by
  intro range hmem
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
  exact h original horiginal

/-! ### The merge is sorted -/

/-- Every range the merge emits starts no earlier than the ranges it was merged from. -/
private theorem Range.startsFrom_mergeSteps {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
    (m : Nat) :
    ∀ (steps : Nat) (a : List (Range α)) (b : List (Range β)),
      Range.chainOK a = true → Range.chainOK b = true →
      Range.StartsFrom m a → Range.StartsFrom m b →
        Range.StartsFrom m (Range.mergeSteps f da db steps a b)
  | 0, _, _, _, _, _, _ => fun _ hmem => absurd hmem (by simp [Range.mergeSteps])
  | _ + 1, [], b, _, _, _, hb => by
    simp only [Range.mergeSteps]
    exact Range.startsFrom_map_mapValue _ hb
  | _ + 1, x :: a, [], _, _, ha, _ => by
    simp only [Range.mergeSteps]
    exact Range.startsFrom_map_mapValue _ ha
  | steps + 1, x :: a, y :: b, hsa, hsb, hxa, hyb => by
    obtain ⟨hx, ha⟩ := Range.startsFrom_cons.mp hxa
    obtain ⟨hy, hb⟩ := Range.startsFrom_cons.mp hyb
    have hxlo := Range.chainOK_cons_lo_le_hi hsa
    have hylo := Range.chainOK_cons_lo_le_hi hsb
    have hsa' := Range.chainOK_of_cons hsa
    have hsb' := Range.chainOK_of_cons hsb
    have recur := Range.startsFrom_mergeSteps f da db m steps
    simp only [Range.mergeSteps]
    split
    · split
      · exact Range.startsFrom_cons.mpr ⟨hx, recur _ _ hsa' hsb ha hyb⟩
      · exact Range.startsFrom_cons.mpr
          ⟨hx, recur _ _ (Range.chainOK_trim _ (by omega) hsa) hsb
            (Range.startsFrom_cons.mpr ⟨by range_omega, ha⟩) hyb⟩
    · split
      · split
        · exact Range.startsFrom_cons.mpr ⟨hy, recur _ _ hsa hsb' hxa hb⟩
        · exact Range.startsFrom_cons.mpr
            ⟨hy, recur _ _ hsa (Range.chainOK_trim _ (by omega) hsb) hxa
              (Range.startsFrom_cons.mpr ⟨by range_omega, hb⟩)⟩
      · split
        · exact Range.startsFrom_cons.mpr
            ⟨hx, recur _ _ hsa' (Range.chainOK_trim _ (by omega) hsb) ha
              (Range.startsFrom_cons.mpr ⟨by range_omega, hb⟩)⟩
        · split
          · exact Range.startsFrom_cons.mpr
              ⟨hx, recur _ _ (Range.chainOK_trim _ (by omega) hsa) hsb'
                (Range.startsFrom_cons.mpr ⟨by range_omega, ha⟩) hb⟩
          · exact Range.startsFrom_cons.mpr ⟨hx, recur _ _ hsa' hsb' ha hb⟩

/-- On sorted lists, the merge's output is sorted, whatever the step budget. -/
private theorem Range.chainOK_mergeSteps {α β γ : Type} (f : α → β → γ) (da : α) (db : β) :
    ∀ (steps : Nat) (a : List (Range α)) (b : List (Range β)),
      Range.chainOK a = true → Range.chainOK b = true →
        Range.chainOK (Range.mergeSteps f da db steps a b) = true
  | 0, _, _, _, _ => rfl
  | _ + 1, [], b, _, hb => by
    simp only [Range.mergeSteps]
    rw [Range.chainOK_map_mapValue]
    exact hb
  | _ + 1, x :: a, [], ha, _ => by
    simp only [Range.mergeSteps]
    rw [Range.chainOK_map_mapValue]
    exact ha
  | steps + 1, x :: a, y :: b, ha, hb => by
    have hxlo := Range.chainOK_cons_lo_le_hi ha
    have hylo := Range.chainOK_cons_lo_le_hi hb
    have hafter := Range.chainOK_cons_startsFrom x a ha
    have hbfter := Range.chainOK_cons_startsFrom y b hb
    have ha' := Range.chainOK_of_cons ha
    have hb' := Range.chainOK_of_cons hb
    have recur := Range.chainOK_mergeSteps f da db steps
    have starts := Range.startsFrom_mergeSteps f da db
    -- `x :: a` starts from any `m` up to `x.lo`, and so does it with `x` cut to start at `lo`,
    -- for any `m` up to `lo`; the same holds for `y :: b`.
    have hxa : ∀ m, m ≤ x.lo → Range.StartsFrom m (x :: a) := fun m hm =>
      Range.startsFrom_cons.mpr ⟨hm, Range.startsFrom_mono (by omega) hafter⟩
    have hyb : ∀ m, m ≤ y.lo → Range.StartsFrom m (y :: b) := fun m hm =>
      Range.startsFrom_cons.mpr ⟨hm, Range.startsFrom_mono (by omega) hbfter⟩
    have hxa' : ∀ m lo, m ≤ lo → lo ≤ x.hi →
        Range.StartsFrom m ({ lo := lo, hi := x.hi, value := x.value } :: a) := fun m lo hm _ =>
      Range.startsFrom_cons.mpr ⟨hm, Range.startsFrom_mono (by range_omega) hafter⟩
    have hyb' : ∀ m lo, m ≤ lo → lo ≤ y.hi →
        Range.StartsFrom m ({ lo := lo, hi := y.hi, value := y.value } :: b) := fun m lo hm _ =>
      Range.startsFrom_cons.mpr ⟨hm, Range.startsFrom_mono (by range_omega) hbfter⟩
    simp only [Range.mergeSteps]
    split
    · split
      · exact Range.chainOK_cons hxlo
          (starts _ steps _ _ ha' hb hafter (hyb _ (by range_omega))) (recur _ _ ha' hb)
      · have hx' := Range.chainOK_trim y.lo (by omega) ha
        exact Range.chainOK_cons (by range_omega)
          (starts _ steps _ _ hx' hb (hxa' _ _ (by range_omega) (by omega))
            (hyb _ (by range_omega)))
          (recur _ _ hx' hb)
    · split
      · split
        · exact Range.chainOK_cons hylo
            (starts _ steps _ _ ha hb' (hxa _ (by range_omega)) hbfter) (recur _ _ ha hb')
        · have hy' := Range.chainOK_trim x.lo (by omega) hb
          exact Range.chainOK_cons (by range_omega)
            (starts _ steps _ _ ha hy' (hxa _ (by range_omega))
              (hyb' _ _ (by range_omega) (by omega)))
            (recur _ _ ha hy')
      · split
        · have hy' := Range.chainOK_trim (x.hi + 1) (by omega) hb
          exact Range.chainOK_cons (by range_omega)
            (starts _ steps _ _ ha' hy' hafter (hyb' _ _ (by range_omega) (by omega)))
            (recur _ _ ha' hy')
        · split
          · have hx' := Range.chainOK_trim (y.hi + 1) (by omega) ha
            exact Range.chainOK_cons (by range_omega)
              (starts _ steps _ _ hx' hb' (hxa' _ _ (by range_omega) (by omega)) hbfter)
              (recur _ _ hx' hb')
          · exact Range.chainOK_cons (by range_omega)
              (starts _ steps _ _ ha' hb' hafter (Range.startsFrom_mono (by range_omega) hbfter))
              (recur _ _ ha' hb')

/-- The merge of two sorted range lists is sorted. -/
theorem Range.chainOK_mergeWith {α β γ : Type} {f : α → β → γ} {da : α} {db : β}
    {a : List (Range α)} {b : List (Range β)}
    (ha : Range.chainOK a = true) (hb : Range.chainOK b = true) :
    Range.chainOK (Range.mergeWith f da db a b) = true :=
  Range.chainOK_mergeSteps f da db _ a b ha hb

/-! ### A scan of the merge reads both lists -/

private theorem Range.scanList_cons_of_holds {α : Type} (range : Range α) {default : α}
    {ranges : List (Range α)} {n : Nat} (h : range.lo ≤ n ∧ n ≤ range.hi) :
    Range.scanList default (range :: ranges) n = range.value := by
  simp only [Range.scanList]
  split
  · rfl
  · contradiction

private theorem Range.scanList_cons_of_not_holds {α : Type} (range : Range α) {default : α}
    {ranges : List (Range α)} {n : Nat} (h : ¬ (range.lo ≤ n ∧ n ≤ range.hi)) :
    Range.scanList default (range :: ranges) n = Range.scanList default ranges n := by
  simp only [Range.scanList]
  split
  · contradiction
  · rfl

private theorem Range.scanList_map_mapValue {α β : Type} (g : α → β) (default : α) (n : Nat) :
    ∀ (ranges : List (Range α)),
      Range.scanList (g default) (ranges.map (Range.mapValue g)) n =
        g (Range.scanList default ranges n)
  | [] => rfl
  | range :: rest => by
    simp only [List.map_cons, Range.scanList, Range.mapValue]
    split <;> simp [Range.scanList_map_mapValue g default n rest]

/-- A scan finds nothing below the start of every range in the list. -/
private theorem Range.scanList_of_startsFrom {α : Type} (default : α) {n m : Nat}
    (hn : n < m) : ∀ {ranges : List (Range α)}, Range.StartsFrom m ranges →
      Range.scanList default ranges n = default
  | [], _ => rfl
  | range :: rest, h => by
    have hlo := (Range.startsFrom_cons.mp h).1
    rw [Range.scanList_cons_of_not_holds range (by omega)]
    exact Range.scanList_of_startsFrom default hn (Range.startsFrom_cons.mp h).2

/-- A sorted list's scan finds nothing below its first range. -/
private theorem Range.scanList_cons_below {α : Type} {default : α} {range : Range α}
    {ranges : List (Range α)} (h : Range.chainOK (range :: ranges) = true) {n : Nat}
    (hn : n < range.lo) : Range.scanList default (range :: ranges) n = default := by
  have hlo := Range.chainOK_cons_lo_le_hi h
  exact Range.scanList_of_startsFrom default hn
    (Range.startsFrom_cons.mpr ⟨Nat.le_refl _,
      Range.startsFrom_mono (by omega) (Range.chainOK_cons_startsFrom range ranges h)⟩)

/-- Moving the start of the first range up to `lo` changes no scan outside the part it cut. -/
private theorem Range.scanList_trim {α : Type} {default : α} (range : Range α)
    (ranges : List (Range α)) {lo n : Nat} (hlo : range.lo ≤ lo) (hn : n < range.lo ∨ lo ≤ n) :
    Range.scanList default ({ lo := lo, hi := range.hi, value := range.value } :: ranges) n =
      Range.scanList default (range :: ranges) n := by
  by_cases h : range.lo ≤ n ∧ n ≤ range.hi
  · rw [Range.scanList_cons_of_holds _ (by range_omega), Range.scanList_cons_of_holds _ h]
  · rw [Range.scanList_cons_of_not_holds _ (by range_omega), Range.scanList_cons_of_not_holds _ h]

/-- On sorted lists, with a step budget no smaller than `Range.mergeBudget`, a scan of the
merge gives `f` of the two lists' scans. -/
private theorem Range.scanList_mergeSteps {α β γ : Type} (f : α → β → γ) (da : α) (db : β)
    (n : Nat) :
    ∀ (steps : Nat) (a : List (Range α)) (b : List (Range β)),
      Range.mergeBudget a b ≤ steps → Range.chainOK a = true → Range.chainOK b = true →
        Range.scanList (f da db) (Range.mergeSteps f da db steps a b) n =
          f (Range.scanList da a n) (Range.scanList db b n)
  | 0, [], [], _, _, _ => rfl
  | 0, x :: a, b, hsteps, _, _ => by
    cases b with
    | nil => simp [Range.mergeBudget] at hsteps
    | cons y b => have := Range.mergeBudget_cons x a y b; omega
  | 0, [], y :: b, hsteps, _, _ => by simp [Range.mergeBudget] at hsteps
  | _ + 1, [], b, _, _, _ => by
    simp only [Range.mergeSteps]
    exact Range.scanList_map_mapValue (f da) db n b
  | _ + 1, x :: a, [], _, _, _ => by
    simp only [Range.mergeSteps]
    exact Range.scanList_map_mapValue (f · db) da n (x :: a)
  | steps + 1, x :: a, y :: b, hsteps, ha, hb => by
    have hxlo := Range.chainOK_cons_lo_le_hi ha
    have hylo := Range.chainOK_cons_lo_le_hi hb
    have ha' := Range.chainOK_of_cons ha
    have hb' := Range.chainOK_of_cons hb
    have hcons := Range.mergeBudget_cons x a y b
    have hbudget_a := Range.mergeBudget_le a (y :: b)
    have hbudget_b := Range.mergeBudget_le (x :: a) b
    have hbudget_ab := Range.mergeBudget_le a b
    simp only [List.length_cons] at hbudget_a hbudget_b
    have recur := Range.scanList_mergeSteps f da db n steps
    simp only [Range.mergeSteps]
    split
    · rename_i hxy
      split
      · -- `x` ends before `y` starts: emit all of `x`.
        rename_i hxend
        by_cases hin : x.lo ≤ n ∧ n ≤ x.hi
        · rw [Range.scanList_cons_of_holds { lo := x.lo, hi := x.hi, value := f x.value db } hin,
            Range.scanList_cons_of_holds x hin, Range.scanList_cons_below hb (by omega)]
        · rw [Range.scanList_cons_of_not_holds
              { lo := x.lo, hi := x.hi, value := f x.value db } hin,
            Range.scanList_cons_of_not_holds x hin, recur _ _ (by omega) ha' hb]
      · -- `y` starts inside `x`: emit `x` up to where `y` starts.
        rename_i hxend
        by_cases hin : x.lo ≤ n ∧ n ≤ y.lo - 1
        · rw [Range.scanList_cons_of_holds
              { lo := x.lo, hi := y.lo - 1, value := f x.value db } hin,
            Range.scanList_cons_of_holds x (by omega), Range.scanList_cons_below hb (by omega)]
        · have hbudget : Range.mergeBudget
              ({ lo := y.lo, hi := x.hi, value := x.value } :: a) (y :: b) ≤ steps := by
            simp [Range.mergeBudget, Nat.ne_of_lt hxy] at hsteps ⊢
            omega
          rw [Range.scanList_cons_of_not_holds
              { lo := x.lo, hi := y.lo - 1, value := f x.value db } hin,
            recur _ _ hbudget (Range.chainOK_trim _ (by omega) ha) hb,
            Range.scanList_trim x a (Nat.le_of_lt hxy) (by omega)]
    · rename_i hxy
      split
      · rename_i hyx
        split
        · -- `y` ends before `x` starts: emit all of `y`.
          rename_i hyend
          by_cases hin : y.lo ≤ n ∧ n ≤ y.hi
          · rw [Range.scanList_cons_of_holds
                { lo := y.lo, hi := y.hi, value := f da y.value } hin,
              Range.scanList_cons_of_holds y hin, Range.scanList_cons_below ha (by omega)]
          · rw [Range.scanList_cons_of_not_holds
                { lo := y.lo, hi := y.hi, value := f da y.value } hin,
              Range.scanList_cons_of_not_holds y hin, recur _ _ (by omega) ha hb']
        · -- `x` starts inside `y`: emit `y` up to where `x` starts.
          rename_i hyend
          by_cases hin : y.lo ≤ n ∧ n ≤ x.lo - 1
          · rw [Range.scanList_cons_of_holds
                { lo := y.lo, hi := x.lo - 1, value := f da y.value } hin,
              Range.scanList_cons_of_holds y (by omega), Range.scanList_cons_below ha (by omega)]
          · have hbudget : Range.mergeBudget (x :: a)
                ({ lo := x.lo, hi := y.hi, value := y.value } :: b) ≤ steps := by
              simp [Range.mergeBudget, Ne.symm (Nat.ne_of_lt hyx)] at hsteps ⊢
              omega
            rw [Range.scanList_cons_of_not_holds
                { lo := y.lo, hi := x.lo - 1, value := f da y.value } hin,
              recur _ _ hbudget ha (Range.chainOK_trim _ (by omega) hb),
              Range.scanList_trim y b (Nat.le_of_lt hyx) (by omega)]
      · -- Both start together: emit their common part.
        rename_i hyx
        split
        · rename_i hends
          by_cases hin : x.lo ≤ n ∧ n ≤ x.hi
          · rw [Range.scanList_cons_of_holds
                { lo := x.lo, hi := x.hi, value := f x.value y.value } hin,
              Range.scanList_cons_of_holds x hin, Range.scanList_cons_of_holds y (by omega)]
          · have hbudget : Range.mergeBudget a
                ({ lo := x.hi + 1, hi := y.hi, value := y.value } :: b) ≤ steps := by
              have := Range.mergeBudget_le a
                ({ lo := x.hi + 1, hi := y.hi, value := y.value } :: b)
              simp only [List.length_cons] at this
              omega
            rw [Range.scanList_cons_of_not_holds
                { lo := x.lo, hi := x.hi, value := f x.value y.value } hin,
              Range.scanList_cons_of_not_holds x hin,
              recur _ _ hbudget ha' (Range.chainOK_trim _ (by omega) hb),
              Range.scanList_trim y b (by omega) (by omega)]
        · rename_i hends
          split
          · rename_i hends'
            by_cases hin : x.lo ≤ n ∧ n ≤ y.hi
            · rw [Range.scanList_cons_of_holds
                  { lo := x.lo, hi := y.hi, value := f x.value y.value } hin,
                Range.scanList_cons_of_holds x (by omega),
                Range.scanList_cons_of_holds y (by omega)]
            · have hbudget : Range.mergeBudget
                  ({ lo := y.hi + 1, hi := x.hi, value := x.value } :: a) b ≤ steps := by
                have := Range.mergeBudget_le
                  ({ lo := y.hi + 1, hi := x.hi, value := x.value } :: a) b
                simp only [List.length_cons] at this
                omega
              rw [Range.scanList_cons_of_not_holds
                  { lo := x.lo, hi := y.hi, value := f x.value y.value } hin,
                Range.scanList_cons_of_not_holds y (by omega),
                recur _ _ hbudget (Range.chainOK_trim _ (by omega) ha) hb',
                Range.scanList_trim x a (by omega) (by omega)]
          · rename_i hends'
            by_cases hin : x.lo ≤ n ∧ n ≤ x.hi
            · rw [Range.scanList_cons_of_holds
                  { lo := x.lo, hi := x.hi, value := f x.value y.value } hin,
                Range.scanList_cons_of_holds x hin, Range.scanList_cons_of_holds y (by omega)]
            · rw [Range.scanList_cons_of_not_holds
                  { lo := x.lo, hi := x.hi, value := f x.value y.value } hin,
                Range.scanList_cons_of_not_holds x hin,
                Range.scanList_cons_of_not_holds y (by omega),
                recur _ _ (by omega) ha' hb']

/-- On sorted lists, a scan of the merge gives, at every code point `n`, `f` of the two lists'
scans. -/
theorem Range.scanList_mergeWith {α β γ : Type} {f : α → β → γ} {da : α} {db : β}
    {a : List (Range α)} {b : List (Range β)}
    (ha : Range.chainOK a = true) (hb : Range.chainOK b = true) (n : Nat) :
    Range.scanList (f da db) (Range.mergeWith f da db a b) n =
      f (Range.scanList da a n) (Range.scanList db b n) :=
  Range.scanList_mergeSteps f da db n _ a b (Range.mergeBudget_le a b) ha hb

/-! ### The combined property table -/

/-- The `Props` of a code point no table has a range for: the defaults `gcbOf`, `extPictOf`
and `incbOf` fall back to. -/
def propsDefault : Props := { gcb := .other, extPict := false, incb := .none }

/-- Puts a `Grapheme_Cluster_Break` and `Extended_Pictographic` pair and an
`Indic_Conjunct_Break` value together into one `Props`. -/
def propsOfPair (gcbExtPict : GCB × Bool) (incb : InCB) : Props :=
  { gcb := gcbExtPict.1, extPict := gcbExtPict.2, incb := incb }

/--
The three property tables merged into one sorted table, each range carrying a whole `Props`.
It is a top-level constant, so compiled code builds it once.
-/
def propsRanges : Array (Range Props) :=
  (Range.mergeWith propsOfPair (.other, false) .none
    (Range.mergeWith Prod.mk .other false gcbRanges.toList extPictRanges.toList)
    incbRanges.toList).toArray

/-- `propsRanges` is sorted by `lo` with no overlapping ranges. -/
theorem propsRanges_sorted : Range.Sorted propsRanges := by
  rw [Range.Sorted, propsRanges, List.toList_toArray]
  exact Range.chainOK_mergeWith (Range.chainOK_mergeWith gcbRanges_sorted extPictRanges_sorted)
    incbRanges_sorted

/-- All three properties of `c`, read with one binary search in `propsRanges`. -/
def propsLookup (c : Char) : Props := Range.lookup propsDefault propsRanges c.toNat

/-- `propsLookup` gives the same properties as `props`, for every character. -/
theorem propsLookup_eq_props (c : Char) : propsLookup c = props c := by
  rw [propsLookup, Range.lookup_eq_scan propsRanges_sorted, props_eq_scan, Range.scan,
    propsRanges, List.toList_toArray]
  -- `propsDefault` is `propsOfPair (.other, false) .none`, the default the merge lemma reads.
  change Range.scanList (propsOfPair (.other, false) .none) _ c.toNat = _
  rw [Range.scanList_mergeWith
      (Range.chainOK_mergeWith gcbRanges_sorted extPictRanges_sorted) incbRanges_sorted,
    Range.scanList_mergeWith gcbRanges_sorted extPictRanges_sorted]
  rfl

end Segmentation.Tables
