import Segmentation.Statements
import Segmentation.Graphemes

/-!
# The scan state summarises the rules' left sides

`breaksBefore` decides with the flags of `ScanState`, while `Segmentation.rules` states each
rule's left side as a pattern over the whole text before the position. This file proves that
each flag, after the scan has read a text, holds exactly when its rule's left side matches that
text: `prev` is the last code point, `linkerTail` is GB9c's left side, `pictTail` is the run that
GB11 extends, `zwjAfterPict` is GB11's left side and `riOdd` is GB12's or GB13's.

`ScanState.push` adds one code point at the end of the text, so every proof here reads a pattern
match from its right end. The `Pat.Matches` lemmas first turn each pattern into a plain statement
about lists, then the `snoc` lemmas say what each left side means for `l ++ [q]` in terms of `l`
and `q`. Each flag lemma is then an induction that adds one code point at a time.

With the flags pinned down, `breaksBefore_iff_isBoundary` shows that `breaksBefore` gives the
verdict of `IsBoundary` at every position inside a text, and `isBoundary_zero` and
`isBoundary_length` give the boundaries at its two ends (GB1 and GB2). Everything is generic over
the property values, so it holds for any property lookup.
-/

namespace Segmentation

/-- The scan state after reading the code points with properties `p :: ps`. -/
def scanStateOf (p : Props) (ps : List Props) : ScanState :=
  ps.foldl ScanState.push (ScanState.start p)

/-! ## Patterns as statements about lists -/

theorem Pat.matches_one_iff {c : Cls} {l : List Props} :
    (Pat.one c).Matches l ↔ ∃ x, l = [x] ∧ c x = true := by
  constructor
  · intro h
    cases h with
    | one hx => exact ⟨_, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩
    exact .one hx

theorem Pat.matches_star_iff {c : Cls} {l : List Props} :
    (Pat.star c).Matches l ↔ ∀ x ∈ l, c x = true := by
  constructor
  · intro h
    generalize hp : Pat.star c = p at h
    induction h with
    | starNil => simp
    | starCons hx _ ih =>
      cases hp
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact ih rfl y hy
    | one => cases hp
    | pairsNil => cases hp
    | pairsCons => cases hp
    | seq => cases hp
  · induction l with
    | nil => intro _; exact .starNil
    | cons x xs ih =>
      intro h
      exact .starCons (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

private theorem matches_pairs_of_all {c : Cls} :
    ∀ (l : List Props), (∀ x ∈ l, c x = true) → l.length % 2 = 0 → (Pat.pairs c).Matches l
  | [], _, _ => .pairsNil
  | [_], _, h => by simp at h
  | x :: y :: rest, hall, hlen =>
    .pairsCons (hall x (by simp)) (hall y (by simp))
      (matches_pairs_of_all rest (fun z hz => hall z (by simp [hz]))
        (by simp at hlen; omega))

theorem Pat.matches_pairs_iff {c : Cls} {l : List Props} :
    (Pat.pairs c).Matches l ↔ (∀ x ∈ l, c x = true) ∧ l.length % 2 = 0 := by
  constructor
  · intro h
    generalize hp : Pat.pairs c = p at h
    induction h with
    | pairsNil => simp
    | pairsCons hx hy _ ih =>
      cases hp
      obtain ⟨hall, hlen⟩ := ih rfl
      refine ⟨?_, by simp; omega⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact hx
      · exact hy
      · exact hall z hz
    | one => cases hp
    | starNil => cases hp
    | starCons => cases hp
    | seq => cases hp
  · rintro ⟨hall, hlen⟩
    exact matches_pairs_of_all l hall hlen

theorem Pat.matches_seq_iff {p q : Pat} {l : List Props} :
    (Pat.seq p q).Matches l ↔ ∃ xs ys, l = xs ++ ys ∧ p.Matches xs ∧ q.Matches ys := by
  constructor
  · intro h
    cases h with
    | seq hp hq => exact ⟨_, _, rfl, hp, hq⟩
  · rintro ⟨xs, ys, rfl, hp, hq⟩
    exact .seq hp hq

/-! ## Left sides read from their right end -/

private theorem snoc_inj {l m : List Props} {q y : Props} (h : l ++ [q] = m ++ [y]) :
    l = m ∧ q = y := by
  simpa using List.append_inj' h rfl

/-- An `ending` left side holds of a text when some suffix of it matches. -/
theorem Left.holds_ending_iff {p : Pat} {l : List Props} :
    Left.Holds (.ending p) l ↔ ∃ a b, l = a ++ b ∧ p.Matches b := Iff.rfl

/-- A code point in `a` followed by a run of `e`: the left side of GB9c, and of GB11 without
its ZWJ. -/
theorem Left.holds_ending_one_star_iff {a e : Cls} {l : List Props} :
    Left.Holds (.ending (.seq (.one a) (.star e))) l ↔
      ∃ pre x ys, l = pre ++ x :: ys ∧ a x = true ∧ ∀ y ∈ ys, e y = true := by
  simp only [Left.holds_ending_iff, Pat.matches_seq_iff, Pat.matches_one_iff,
    Pat.matches_star_iff]
  constructor
  · rintro ⟨pre, _, rfl, _, ys, rfl, ⟨x, rfl, hx⟩, hys⟩
    exact ⟨pre, x, ys, rfl, hx, hys⟩
  · rintro ⟨pre, x, ys, rfl, hx, hys⟩
    exact ⟨pre, x :: ys, rfl, [x], ys, rfl, ⟨x, rfl, hx⟩, hys⟩

theorem Left.holds_ending_one_star_nil {a e : Cls} :
    ¬ Left.Holds (.ending (.seq (.one a) (.star e))) [] := by
  rw [Left.holds_ending_one_star_iff]
  rintro ⟨pre, x, ys, h, -⟩
  simp at h

/-- Adding `q` at the end extends the run when `q` is in `e`, and starts a new one when `q` is
in `a`. -/
theorem Left.holds_ending_one_star_snoc {a e : Cls} {l : List Props} {q : Props} :
    Left.Holds (.ending (.seq (.one a) (.star e))) (l ++ [q]) ↔
      a q = true ∨ (Left.Holds (.ending (.seq (.one a) (.star e))) l ∧ e q = true) := by
  simp only [Left.holds_ending_one_star_iff]
  constructor
  · rintro ⟨pre, x, ys, h, hx, hys⟩
    rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y, rfl⟩
    · obtain ⟨-, rfl⟩ := snoc_inj h
      exact .inl hx
    · simp only [List.concat_eq_append] at h hys
      have h' : l ++ [q] = (pre ++ x :: ys') ++ [y] := by simp [h]
      obtain ⟨rfl, rfl⟩ := snoc_inj h'
      exact .inr ⟨⟨pre, x, ys', rfl, hx, fun z hz => hys z (by simp [hz])⟩,
        hys q (by simp)⟩
  · rintro (hq | ⟨⟨pre, x, ys, rfl, hx, hys⟩, hq⟩)
    · exact ⟨l, q, [], by simp, hq, by simp⟩
    · refine ⟨pre, x, ys ++ [q], by simp, hx, ?_⟩
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hys z hz
      · exact hq

/-- The left side of GB11 holds of `l ++ [q]` exactly when `q` is the ZWJ and `l` ends with the
pictograph and its run of `e`. -/
theorem Left.holds_ending_one_star_one_snoc {a e z : Cls} {l : List Props} {q : Props} :
    Left.Holds (.ending (.seq (.one a) (.seq (.star e) (.one z)))) (l ++ [q]) ↔
      Left.Holds (.ending (.seq (.one a) (.star e))) l ∧ z q = true := by
  rw [Left.holds_ending_one_star_iff]
  simp only [Left.holds_ending_iff, Pat.matches_seq_iff, Pat.matches_one_iff,
    Pat.matches_star_iff]
  constructor
  · rintro ⟨pre, _, h, _, _, rfl, ⟨x, rfl, hx⟩, ys, _, rfl, hys, ⟨w, rfl, hw⟩⟩
    have h' : l ++ [q] = (pre ++ x :: ys) ++ [w] := by simp [h]
    obtain ⟨rfl, rfl⟩ := snoc_inj h'
    exact ⟨⟨pre, x, ys, rfl, hx, hys⟩, hw⟩
  · rintro ⟨⟨pre, x, ys, rfl, hx, hys⟩, hq⟩
    exact ⟨pre, [x] ++ (ys ++ [q]), by simp, [x], ys ++ [q], rfl, ⟨x, rfl, hx⟩,
      ys, [q], rfl, hys, ⟨q, rfl, hq⟩⟩

theorem Left.holds_ending_one_star_one_nil {a e z : Cls} :
    ¬ Left.Holds (.ending (.seq (.one a) (.seq (.star e) (.one z)))) [] := by
  intro h
  have : Left.Holds (.ending (.seq (.one a) (.seq (.star e) (.one z)))) ([] ++ []) := h
  simp only [Left.holds_ending_iff, Pat.matches_seq_iff, Pat.matches_one_iff] at this
  obtain ⟨_, _, h, _, _, rfl, ⟨_, rfl, _⟩, _, _, rfl, _, ⟨_, rfl, _⟩⟩ := this
  simp at h

/-- The run of code points in `c` at the end of `l` has odd length (`odd = true`) or even length
(`odd = false`): either the whole text is that run, or a code point outside `c` comes before it.
-/
def RunParity (c : Cls) (odd : Bool) (l : List Props) : Prop :=
  ((∀ x ∈ l, c x = true) ∧ (l.length % 2 == 1) = odd) ∨
    ∃ a x b, l = a ++ x :: b ∧ c x = false ∧
      (∀ y ∈ b, c y = true) ∧ (b.length % 2 == 1) = odd

private theorem parity_snoc (b : List Props) (q : Props) (odd : Bool) :
    ((b ++ [q]).length % 2 == 1) = odd ↔ (b.length % 2 == 1) = !odd := by
  cases odd <;> simp <;> omega

/-- Adding `q` at the end flips the parity of the run when `q` is in `c`, and starts an empty
(even) run when it is not. -/
theorem RunParity.snoc {c : Cls} {odd : Bool} {l : List Props} {q : Props} :
    RunParity c odd (l ++ [q]) ↔
      (c q = true ∧ RunParity c (!odd) l) ∨ (c q = false ∧ odd = false) := by
  unfold RunParity
  constructor
  · rintro (⟨hall, hlen⟩ | ⟨a, x, b, h, hx, hall, hlen⟩)
    · refine .inl ⟨hall q (by simp), .inl ⟨fun y hy => hall y (by simp [hy]), ?_⟩⟩
      exact (parity_snoc l q odd).1 hlen
    · rcases List.eq_nil_or_concat b with rfl | ⟨b', y, rfl⟩
      · obtain ⟨-, rfl⟩ := snoc_inj h
        exact .inr ⟨hx, by simpa using hlen.symm⟩
      · simp only [List.concat_eq_append] at h hall hlen
        have h' : l ++ [q] = (a ++ x :: b') ++ [y] := by simp [h]
        obtain ⟨rfl, rfl⟩ := snoc_inj h'
        refine .inl ⟨hall q (by simp), .inr ⟨a, x, b', rfl, hx,
          fun z hz => hall z (by simp [hz]), ?_⟩⟩
        exact (parity_snoc b' q odd).1 hlen
  · rintro (⟨hq, ⟨hall, hlen⟩ | ⟨a, x, b, rfl, hx, hall, hlen⟩⟩ | ⟨hq, rfl⟩)
    · refine .inl ⟨?_, (parity_snoc l q odd).2 hlen⟩
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hall z hz
      · exact hq
    · refine .inr ⟨a, x, b ++ [q], by simp, hx, ?_, (parity_snoc b q odd).2 hlen⟩
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hall z hz
      · exact hq
    · exact .inr ⟨l, q, [], by simp, hq, by simp, by simp⟩

theorem RunParity.nil {c : Cls} {odd : Bool} : RunParity c odd [] ↔ odd = false := by
  unfold RunParity
  constructor
  · rintro (⟨-, h⟩ | ⟨a, x, b, h, -⟩)
    · simpa using h.symm
    · simp at h
  · rintro rfl
    exact .inl ⟨by simp, rfl⟩

/-- An odd run of `c` matches `(c c)* c`. -/
theorem Pat.matches_pairs_one_iff {c : Cls} {l : List Props} :
    (Pat.seq (.pairs c) (.one c)).Matches l ↔
      (∀ x ∈ l, c x = true) ∧ (l.length % 2 == 1) = true := by
  simp only [Pat.matches_seq_iff, Pat.matches_pairs_iff, Pat.matches_one_iff]
  constructor
  · rintro ⟨xs, _, rfl, ⟨hall, hlen⟩, x, rfl, hx⟩
    refine ⟨?_, by simp; omega⟩
    intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hall z hz
    · exact hx
  · rintro ⟨hall, hlen⟩
    rcases List.eq_nil_or_concat l with rfl | ⟨xs, x, rfl⟩
    · simp at hlen
    · simp only [List.concat_eq_append] at hall hlen ⊢
      exact ⟨xs, [x], rfl, ⟨fun z hz => hall z (by simp [hz]), by simp at hlen; omega⟩,
        x, rfl, hall x (by simp)⟩

/-- The left sides of GB12 and GB13 together say the run of `c` at the end has odd length. -/
theorem Left.holds_sot_or_notThen_pairs_one_iff {c : Cls} {l : List Props} :
    (Left.Holds (.sot (.seq (.pairs c) (.one c))) l ∨
      Left.Holds (.notThen c (.seq (.pairs c) (.one c))) l) ↔ RunParity c true l := by
  simp only [Left.Holds, Pat.matches_pairs_one_iff, RunParity]

/-! ## The scan state after a text -/

/-- The state before any code point: no run has started. `prev` is a placeholder that the first
`push` replaces. -/
private def blankState (p : Props) : ScanState := ⟨p, false, false, false, false⟩

private theorem scanStateOf_eq_foldl (p : Props) (ps : List Props) :
    scanStateOf p ps = (p :: ps).foldl ScanState.push (blankState p) := rfl

private theorem foldl_push_snoc (s : ScanState) (l : List Props) (q : Props) :
    (l ++ [q]).foldl ScanState.push s = (l.foldl ScanState.push s).push q := by
  simp [List.foldl_append]

/-- Induction that adds one element at the end of the list, the order the scan reads in. -/
private theorem snoc_induction {P : List Props → Prop} (nil : P [])
    (snoc : ∀ l q, P l → P (l ++ [q])) (l : List Props) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons q r ih => rw [List.reverse_cons]; exact snoc _ _ ih

private theorem foldl_push_prev :
    ∀ (s : ScanState) (q : Props) (qs : List Props),
      ((q :: qs).foldl ScanState.push s).prev = (q :: qs).getLast (List.cons_ne_nil q qs)
  | _, _, [] => rfl
  | s, q, q' :: qs => by
    rw [List.foldl_cons, foldl_push_prev (s.push q) q' qs]
    rfl

/-- `prev` is the last code point read. -/
theorem scanStateOf_prev (p : Props) (ps : List Props) :
    (scanStateOf p ps).prev = (p :: ps).getLast (List.cons_ne_nil p ps) :=
  foldl_push_prev _ p ps

private theorem foldl_push_linkerTail (p : Props) (l : List Props) :
    (l.foldl ScanState.push (blankState p)).linkerTail = true ↔
      Left.Holds (.ending (.seq (.one (incbIs .linker)) (.star (incbIs .extend)))) l := by
  induction l using snoc_induction with
  | nil => simp [blankState, Left.holds_ending_one_star_nil]
  | snoc l q ih =>
    rw [foldl_push_snoc, Left.holds_ending_one_star_snoc, ← ih]
    simp [ScanState.push]

/-- `linkerTail` is the left side of GB9c: InCB `Linker` then InCB `Extend*` at the end. -/
theorem scanStateOf_linkerTail (p : Props) (ps : List Props) :
    (scanStateOf p ps).linkerTail = true ↔
      Left.Holds (.ending (.seq (.one (incbIs .linker)) (.star (incbIs .extend)))) (p :: ps) :=
  foldl_push_linkerTail p (p :: ps)

private theorem foldl_push_pictTail (p : Props) (l : List Props) :
    (l.foldl ScanState.push (blankState p)).pictTail = true ↔
      Left.Holds (.ending (.seq (.one isExtPict) (.star (gcbIn [.extend])))) l := by
  induction l using snoc_induction with
  | nil => simp [blankState, Left.holds_ending_one_star_nil]
  | snoc l q ih =>
    rw [foldl_push_snoc, Left.holds_ending_one_star_snoc, ← ih]
    simp [ScanState.push]

/-- `pictTail` holds when the text ends with an Extended_Pictographic code point then GCB
`Extend*`, the part of GB11's left side before the ZWJ. -/
theorem scanStateOf_pictTail (p : Props) (ps : List Props) :
    (scanStateOf p ps).pictTail = true ↔
      Left.Holds (.ending (.seq (.one isExtPict) (.star (gcbIn [.extend])))) (p :: ps) :=
  foldl_push_pictTail p (p :: ps)

private theorem foldl_push_zwjAfterPict (p : Props) (l : List Props) :
    (l.foldl ScanState.push (blankState p)).zwjAfterPict = true ↔
      Left.Holds (.ending (.seq (.one isExtPict)
        (.seq (.star (gcbIn [.extend])) (.one (gcbIn [.zwj]))))) l := by
  induction l using snoc_induction with
  | nil => simp [blankState, Left.holds_ending_one_star_one_nil]
  | snoc l q _ =>
    rw [foldl_push_snoc, Left.holds_ending_one_star_one_snoc, ← foldl_push_pictTail p l]
    simp [ScanState.push]

/-- `zwjAfterPict` is the left side of GB11: Extended_Pictographic, GCB `Extend*`, GCB `ZWJ` at
the end. -/
theorem scanStateOf_zwjAfterPict (p : Props) (ps : List Props) :
    (scanStateOf p ps).zwjAfterPict = true ↔
      Left.Holds (.ending (.seq (.one isExtPict)
        (.seq (.star (gcbIn [.extend])) (.one (gcbIn [.zwj]))))) (p :: ps) :=
  foldl_push_zwjAfterPict p (p :: ps)

/-- `riOdd` tracks both parities at once, because `push` reads the previous parity to flip it. -/
private theorem foldl_push_riOdd (p : Props) (l : List Props) :
    ((l.foldl ScanState.push (blankState p)).riOdd = true ↔
        RunParity (gcbIn [.regionalIndicator]) true l) ∧
      ((l.foldl ScanState.push (blankState p)).riOdd = false ↔
        RunParity (gcbIn [.regionalIndicator]) false l) := by
  induction l using snoc_induction with
  | nil => simp [blankState, RunParity.nil]
  | snoc l q ih =>
    rw [foldl_push_snoc, RunParity.snoc, RunParity.snoc]
    simp only [Bool.not_true, Bool.not_false, ← ih.1, ← ih.2, ScanState.push]
    cases gcbIn [.regionalIndicator] q <;> cases (l.foldl ScanState.push (blankState p)).riOdd <;>
      simp

/-- `riOdd` is the left side of GB12 or of GB13: the run of GCB `RI` at the end has odd length,
and either it is the whole text or a code point outside `RI` comes before it. -/
theorem scanStateOf_riOdd (p : Props) (ps : List Props) :
    (scanStateOf p ps).riOdd = true ↔
      Left.Holds (.sot (.seq (.pairs (gcbIn [.regionalIndicator]))
        (.one (gcbIn [.regionalIndicator])))) (p :: ps) ∨
      Left.Holds (.notThen (gcbIn [.regionalIndicator])
        (.seq (.pairs (gcbIn [.regionalIndicator])) (.one (gcbIn [.regionalIndicator]))))
        (p :: ps) := by
  rw [Left.holds_sot_or_notThen_pairs_one_iff]
  exact (foldl_push_riOdd p (p :: ps)).1

/-! ## The decision at a position inside the text -/

private theorem scanStateOf_snoc (p q : Props) (ps : List Props) :
    scanStateOf p (ps ++ [q]) = (scanStateOf p ps).push q :=
  foldl_push_snoc _ _ _

/-- A one-code-point `ending` left side, as in GB3 to GB9b, reads only `prev`. -/
theorem Left.holds_ending_one_cons_iff {cl : Cls} {p : Props} {ps : List Props} :
    Left.Holds (.ending (.one cl)) (p :: ps) ↔ cl (scanStateOf p ps).prev = true := by
  simp only [Left.holds_ending_iff, Pat.matches_one_iff]
  rcases List.eq_nil_or_concat ps with rfl | ⟨ps', q, rfl⟩
  · constructor
    · rintro ⟨a, _, h, x, rfl, hx⟩
      obtain ⟨-, rfl⟩ := snoc_inj (l := []) h
      exact hx
    · intro h
      exact ⟨[], [p], rfl, p, rfl, h⟩
  · simp only [List.concat_eq_append, scanStateOf_snoc]
    constructor
    · rintro ⟨a, _, h, x, rfl, hx⟩
      obtain ⟨-, rfl⟩ := snoc_inj (l := p :: ps') h
      exact hx
    · intro h
      exact ⟨p :: ps', [q], rfl, q, rfl, h⟩

private theorem left_any_iff {l : List Props} : Left.Holds .any l ↔ True := Iff.rfl

private theorem right_any_iff {l : List Props} : Right.Holds .any l ↔ True := Iff.rfl

private theorem right_eot_cons_iff {n : Props} {rest : List Props} :
    Right.Holds .eot (n :: rest) ↔ False := by
  simp [Right.Holds]

private theorem right_one_cons_iff {cl : Cls} {n : Props} {rest : List Props} :
    Right.Holds (.one cl) (n :: rest) ↔ cl n = true := by
  simp [Right.Holds]

/-- GB1's left side, `sot nothing`, holds only before the first code point. -/
private theorem not_sot_nothing (p : Props) (ps : List Props) :
    ¬ Left.Holds (.sot nothing) (p :: ps) := by
  intro h
  have := Pat.matches_star_iff.mp h p (by simp)
  simp at this

/-- GB12 and GB13 are both no-break rules with the same right side, so the first-match reading
only needs to know whether either applies; this merges them as `breakRows` does. -/
private theorem not_and_not_and_iff {P Q R X : Prop} :
    (¬ (P ∧ R) ∧ ¬ (Q ∧ R) ∧ X) ↔ (¬ ((P ∨ Q) ∧ R) ∧ X) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- The body of `IsBoundary`, over any list of rules and any meaning of "applies": some rule
says ÷, applies, and no earlier rule applies. -/
private def FirstBreak (applies : Rule → Prop) (l : List Rule) : Prop :=
  ∃ (k : Nat) (r : Rule), l[k]? = some r ∧ applies r ∧ r.verdict = .brk ∧
    ∀ (j : Nat) (r' : Rule), j < k → l[j]? = some r' → ¬ applies r'

private theorem firstBreak_nil {applies : Rule → Prop} : FirstBreak applies [] ↔ False := by
  simp [FirstBreak]

private theorem firstBreak_cons {applies : Rule → Prop} {r : Rule} {l : List Rule} :
    FirstBreak applies (r :: l) ↔
      (applies r ∧ r.verdict = .brk) ∨ (¬ applies r ∧ FirstBreak applies l) := by
  constructor
  · rintro ⟨k, r', hk, ha, hv, hearlier⟩
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact .inl ⟨ha, hv⟩
    | succ k =>
      refine .inr ⟨hearlier 0 r (by omega) rfl, k, r', hk, ha, hv, ?_⟩
      intro j r'' hj hr''
      exact hearlier (j + 1) r'' (by omega) hr''
  · rintro (⟨ha, hv⟩ | ⟨hna, k, r', hk, ha, hv, hearlier⟩)
    · exact ⟨0, r, rfl, ha, hv, fun j _ hj _ => absurd hj (Nat.not_lt_zero j)⟩
    · refine ⟨k + 1, r', hk, ha, hv, ?_⟩
      intro j r'' hj hr''
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr''
        subst hr''
        exact hna
      | succ j => exact hearlier j r'' (by omega) hr''

private theorem firstBreak_cons_brk {applies : Rule → Prop} {r : Rule} {l : List Rule}
    (h : r.verdict = .brk) :
    FirstBreak applies (r :: l) ↔ applies r ∨ FirstBreak applies l := by
  rw [firstBreak_cons, h]
  by_cases ha : applies r <;> simp [ha]

private theorem firstBreak_cons_noBrk {applies : Rule → Prop} {r : Rule} {l : List Rule}
    (h : r.verdict = .noBrk) :
    FirstBreak applies (r :: l) ↔ ¬ applies r ∧ FirstBreak applies l := by
  rw [firstBreak_cons, h]
  simp

/-- The decision of `breakRows` after `p :: ps`, before `n`, is the first-match reading of
`rules` with `p :: ps` before the position and `n :: rest` after it. The rules are unfolded one
by one, each left and right side is turned into the `ScanState` test of its row, and the two
first-match chains are then compared on every value of the twelve row tests. -/
private theorem breaksBefore_iff_firstBreak (p : Props) (ps : List Props) (n : Props)
    (rest : List Props) :
    breaksBefore (scanStateOf p ps) n = true ↔
      FirstBreak (fun r => r.left.Holds (p :: ps) ∧ r.right.Holds (n :: rest)) rules := by
  unfold rules
  simp only [firstBreak_cons_brk, firstBreak_cons_noBrk, firstBreak_nil]
  simp only [not_and_not_and_iff]
  simp only [Left.holds_ending_one_cons_iff, ← scanStateOf_linkerTail,
    ← scanStateOf_zwjAfterPict,
    ← scanStateOf_riOdd, right_one_cons_iff, not_sot_nothing, anyCp, left_any_iff, right_any_iff,
    right_eot_cons_iff, and_false, and_true, true_and, false_or, or_false, ← Bool.and_eq_true]
  unfold breaksBefore breakRows
  simp only [List.find?]
  generalize (gcbIn [GCB.cr] (scanStateOf p ps).prev && gcbIn [GCB.lf] n) = b0
  generalize (gcbIn [GCB.control, GCB.cr, GCB.lf] (scanStateOf p ps).prev) = b1
  generalize (gcbIn [GCB.control, GCB.cr, GCB.lf] n) = b2
  generalize
    (gcbIn [GCB.l] (scanStateOf p ps).prev && gcbIn [GCB.l, GCB.v, GCB.lv, GCB.lvt] n) = b3
  generalize (gcbIn [GCB.lv, GCB.v] (scanStateOf p ps).prev && gcbIn [GCB.v, GCB.t] n) = b4
  generalize (gcbIn [GCB.lvt, GCB.t] (scanStateOf p ps).prev && gcbIn [GCB.t] n) = b5
  generalize (gcbIn [GCB.extend, GCB.zwj] n) = b6
  generalize (gcbIn [GCB.spacingMark] n) = b7
  generalize (gcbIn [GCB.prepend] (scanStateOf p ps).prev) = b8
  generalize ((scanStateOf p ps).linkerTail && incbIs InCB.consonant n) = b9
  generalize ((scanStateOf p ps).zwjAfterPict && isExtPict n) = b10
  generalize ((scanStateOf p ps).riOdd && gcbIn [GCB.regionalIndicator] n) = b11
  cases b0 <;> simp only [Bool.false_eq_true, Bool.not_eq_true, not_false_eq_true,
    not_true_eq_false, true_and, false_and] <;>
  cases b1 <;> simp only [Bool.false_eq_true, false_or, true_or] <;>
  cases b2 <;> simp only [Bool.false_eq_true, false_or, true_or] <;>
  cases b3 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b4 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b5 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b6 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b7 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b8 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b9 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b10 <;> simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, false_and] <;>
  cases b11 <;> simp only [Bool.false_eq_true, Bool.true_eq_false]

/-- At a position inside a non-empty text, after `c` and the first `i` code points of `cs` and
before `cs[i]`, `breaksBefore` on the scan state says ÷ exactly when UAX #29 puts a boundary
there. GB1 and GB2 never apply inside the text and GB999 always does; GB3 to GB11 are the rows
of `breakRows` in order, and GB12 and GB13 together are its last row. -/
theorem breaksBefore_iff_isBoundary (props : Char → Props) (c : Char) (cs : List Char) (i : Nat)
    (hi : i < cs.length) :
    breaksBefore (scanStateOf (props c) ((cs.take i).map props)) (props cs[i]) = true ↔
      IsBoundary props (c :: cs) (i + 1) := by
  have hpre : ((c :: cs).take (i + 1)).map props = props c :: (cs.take i).map props := by simp
  have hpost : ((c :: cs).drop (i + 1)).map props =
      props cs[i] :: (cs.drop (i + 1)).map props := by
    rw [List.drop_succ_cons, List.drop_eq_getElem_cons hi, List.map_cons]
  rw [breaksBefore_iff_firstBreak (rest := (cs.drop (i + 1)).map props)]
  simp only [IsBoundary, Rule.Applies, hpre, hpost]
  rfl

/-- The start of a non-empty text is a boundary, by GB1. -/
theorem isBoundary_zero (props : Char → Props) (cs : List Char) (h : cs ≠ []) :
    IsBoundary props cs 0 := by
  obtain ⟨c, cs', rfl⟩ := List.exists_cons_of_ne_nil h
  refine ⟨0, _, rfl, ⟨Pat.Matches.starNil, props c, cs'.map props, by simp, rfl⟩, rfl, ?_⟩
  intro j _ hj _
  exact absurd hj (Nat.not_lt_zero j)

/-- The end of a non-empty text is a boundary, by GB2: GB1, the only rule before it, needs the
text before the position to be empty. -/
theorem isBoundary_length (props : Char → Props) (cs : List Char) (h : cs ≠ []) :
    IsBoundary props cs cs.length := by
  rcases List.eq_nil_or_concat cs with rfl | ⟨l, x, rfl⟩
  · exact absurd rfl h
  simp only [List.concat_eq_append] at h ⊢
  refine ⟨1, _, rfl, ⟨⟨l.map props, [props x],
    by simp only [List.take_length, List.map_append, List.map_cons, List.map_nil], .one rfl⟩,
    by simp [Right.Holds]⟩, rfl, ?_⟩
  intro j r' hj hr' happ
  obtain rfl : j = 0 := by omega
  obtain rfl : r' = _ := (Option.some.inj hr').symm
  obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil (by simp : (l ++ [x]).map props ≠ [])
  have hleft := happ.1
  simp only [List.take_length] at hleft
  rw [hys] at hleft
  exact not_sot_nothing y ys hleft

end Segmentation
