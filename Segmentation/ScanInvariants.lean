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
and `q`. Each flag lemma is then an induction that adds one code point at a time. Everything is
generic over the property values, so it holds for any property lookup.
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
    ∃ a x b, l = a ++ x :: b ∧ c x = false ∧ (∀ y ∈ b, c y = true) ∧ (b.length % 2 == 1) = odd

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
      Left.Holds (.ending (.seq (.one (incbIs .Linker)) (.star (incbIs .Extend)))) l := by
  induction l using snoc_induction with
  | nil => simp [blankState, Left.holds_ending_one_star_nil]
  | snoc l q ih =>
    rw [foldl_push_snoc, Left.holds_ending_one_star_snoc, ← ih]
    simp [ScanState.push]

/-- `linkerTail` is the left side of GB9c: InCB `Linker` then InCB `Extend*` at the end. -/
theorem scanStateOf_linkerTail (p : Props) (ps : List Props) :
    (scanStateOf p ps).linkerTail = true ↔
      Left.Holds (.ending (.seq (.one (incbIs .Linker)) (.star (incbIs .Extend)))) (p :: ps) :=
  foldl_push_linkerTail p (p :: ps)

private theorem foldl_push_pictTail (p : Props) (l : List Props) :
    (l.foldl ScanState.push (blankState p)).pictTail = true ↔
      Left.Holds (.ending (.seq (.one isExtPict) (.star (gcbIn [.Extend])))) l := by
  induction l using snoc_induction with
  | nil => simp [blankState, Left.holds_ending_one_star_nil]
  | snoc l q ih =>
    rw [foldl_push_snoc, Left.holds_ending_one_star_snoc, ← ih]
    simp [ScanState.push]

/-- `pictTail` holds when the text ends with an Extended_Pictographic code point then GCB
`Extend*`, the part of GB11's left side before the ZWJ. -/
theorem scanStateOf_pictTail (p : Props) (ps : List Props) :
    (scanStateOf p ps).pictTail = true ↔
      Left.Holds (.ending (.seq (.one isExtPict) (.star (gcbIn [.Extend])))) (p :: ps) :=
  foldl_push_pictTail p (p :: ps)

private theorem foldl_push_zwjAfterPict (p : Props) (l : List Props) :
    (l.foldl ScanState.push (blankState p)).zwjAfterPict = true ↔
      Left.Holds (.ending (.seq (.one isExtPict)
        (.seq (.star (gcbIn [.Extend])) (.one (gcbIn [.ZWJ]))))) l := by
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
        (.seq (.star (gcbIn [.Extend])) (.one (gcbIn [.ZWJ]))))) (p :: ps) :=
  foldl_push_zwjAfterPict p (p :: ps)

/-- `riOdd` tracks both parities at once, because `push` reads the previous parity to flip it. -/
private theorem foldl_push_riOdd (p : Props) (l : List Props) :
    ((l.foldl ScanState.push (blankState p)).riOdd = true ↔ RunParity (gcbIn [.RI]) true l) ∧
      ((l.foldl ScanState.push (blankState p)).riOdd = false ↔
        RunParity (gcbIn [.RI]) false l) := by
  induction l using snoc_induction with
  | nil => simp [blankState, RunParity.nil]
  | snoc l q ih =>
    rw [foldl_push_snoc, RunParity.snoc, RunParity.snoc]
    simp only [Bool.not_true, Bool.not_false, ← ih.1, ← ih.2, ScanState.push]
    cases gcbIn [.RI] q <;> cases (l.foldl ScanState.push (blankState p)).riOdd <;> simp

/-- `riOdd` is the left side of GB12 or of GB13: the run of GCB `RI` at the end has odd length,
and either it is the whole text or a code point outside `RI` comes before it. -/
theorem scanStateOf_riOdd (p : Props) (ps : List Props) :
    (scanStateOf p ps).riOdd = true ↔
      Left.Holds (.sot (.seq (.pairs (gcbIn [.RI])) (.one (gcbIn [.RI])))) (p :: ps) ∨
      Left.Holds (.notThen (gcbIn [.RI]) (.seq (.pairs (gcbIn [.RI])) (.one (gcbIn [.RI]))))
        (p :: ps) := by
  rw [Left.holds_sot_or_notThen_pairs_one_iff]
  exact (foldl_push_riOdd p (p :: ps)).1

end Segmentation
