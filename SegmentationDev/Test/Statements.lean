import Segmentation

/-!
# Checks of the theorem statements

Compile-time checks of `Segmentation.Statements`. The statements are fixed before the
segmenter exists, so these checks pin what a later proof must be applied to: the rule
rows and their order, and the parameters each headline statement takes.
-/

-- "UAX #29 §3.1.1, revision 49, in the standard's order. First match wins."
-- Dropping or reordering a row changes which rule wins, so the order is pinned.
theorem «rules lists GB1 to GB999 in the standard's order» :
    Segmentation.rules.map (·.name) =
      ["GB1", "GB2", "GB3", "GB4", "GB5", "GB6", "GB7", "GB8", "GB9", "GB9a", "GB9b",
       "GB9c", "GB11", "GB12", "GB13", "GB999"] := rfl

/-- `true` for a rule that puts a boundary (÷), `false` for one that forbids it (×). -/
def statementsRuleBreaks (r : Segmentation.Rule) : Bool :=
  match r.verdict with
  | .brk => true
  | .noBrk => false

-- UAX #29 revision 49 marks GB1, GB2, GB4, GB5 and GB999 with ÷ and every other rule with ×.
theorem «rules verdicts break only at GB1 GB2 GB4 GB5 and GB999» :
    Segmentation.rules.map statementsRuleBreaks =
      [true, true, false, true, true, false, false, false, false, false, false,
       false, false, false, false, true] := rfl

open Segmentation in
-- The text before the position is one linker and nothing else. A row that still required
-- a consonant before the linker, as revision 47 did, would make this unprovable.
theorem «GB9c holds after a lone linker with no consonant before it, as revision 49 states» :
    ∃ r, rules[11]? = some r ∧ r.name = "GB9c" ∧
      r.left.Holds [{ gcb := GCB.extend, extPict := false, incb := InCB.linker }] ∧
      r.right.Holds [{ gcb := GCB.other, extPict := false, incb := InCB.consonant }] := by
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · exact (⟨[], [{ gcb := GCB.extend, extPict := false, incb := InCB.linker }] ++ [], rfl,
      Pat.Matches.seq (Pat.Matches.one rfl) Pat.Matches.starNil⟩ :
      ∃ a b, [({ gcb := GCB.extend, extPict := false, incb := InCB.linker } : Props)] = a ++ b ∧
        Pat.Matches (.seq (.one (incbIs .linker)) (.star (incbIs .extend))) b)
  · exact (⟨{ gcb := GCB.other, extPict := false, incb := InCB.consonant }, [], rfl, rfl⟩ :
      ∃ x rest, [({ gcb := GCB.other, extPict := false, incb := InCB.consonant } : Props)] =
        x :: rest ∧ incbIs .consonant x = true)

-- JoinRestoresInput and ClustersNonEmpty mention only `graphemes`, so they must not also demand
-- the property lookup or the boundary function; a stray parameter would make these ascriptions
-- fail.
theorem «JoinRestoresInput depends on the segmenter alone» : True := by
  have _joinRestoresInput : (String → List String) → Prop := Segmentation.JoinRestoresInput
  trivial

theorem «ClustersNonEmpty is stated over the segmenter alone» : True := by
  have _clustersNonEmpty : (String → List String) → Prop := Segmentation.ClustersNonEmpty
  trivial

-- Later proofs apply `CutsMatchRules props graphemes` and
-- `BoundariesMatchCuts graphemes boundaries`. If the section variables were declared in another
-- order, these ascriptions would not type-check.
theorem «CutsMatchRules takes the property lookup first and the segmenter second» : True := by
  have _cutsMatchRules : (Char → Segmentation.Props) → (String → List String) → Prop :=
    Segmentation.CutsMatchRules
  trivial

theorem «BoundariesMatchCuts takes the segmenter first and the boundary function second» :
    True := by
  have _boundariesMatchCuts : (String → List String) → (String → List Nat) → Prop :=
    Segmentation.BoundariesMatchCuts
  trivial

-- "The clusters put back together are the input."
-- A segmenter that returns the whole text as one cluster joins back to the input exactly.
theorem «JoinRestoresInput holds for a segmenter whose clusters join back to the input» :
    Segmentation.JoinRestoresInput (fun s => [s]) := by
  intro s
  first
    | simp [String.join]
    | rfl

-- A segmenter that returns no clusters loses the text "a", so JoinRestoresInput must not hold
-- for it.
theorem «JoinRestoresInput rejects a segmenter that drops the text» :
    ¬ Segmentation.JoinRestoresInput (fun _ => []) := by
  intro h
  have hjoin := h "a"
  first
    | exact absurd hjoin (by decide)
    | simp [String.join] at hjoin

-- "None of the clusters is empty."
theorem «ClustersNonEmpty rejects a segmenter that returns an empty cluster» :
    ¬ Segmentation.ClustersNonEmpty (fun _ => [""]) := by
  intro h
  exact h "" "" (by simp) rfl

-- "At every position of a non-empty text, ends included, a cut falls exactly where UAX #29 puts
-- a boundary. The ends make GB1 and GB2 live in the proof."
-- For the text "a", GB2 puts a boundary at position 1 (the end). A segmenter returning no
-- clusters has cut points [0] only, so CutsMatchRules must not hold for it.
theorem «CutsMatchRules rejects a segmenter that leaves out the end-of-text cut» :
    ¬ Segmentation.CutsMatchRules (fun _ => ⟨.other, false, .none⟩) (fun _ => []) := by
  intro h
  have ht : "a".toList = ['a'] := by first | rfl | decide | simp
  have hb : Segmentation.IsBoundary (fun _ => ⟨.other, false, .none⟩) ['a'] 1 := by
    refine ⟨1, ⟨"GB2", .ending (.one Segmentation.anyCp), .eot, .brk⟩, rfl, ?_, rfl, ?_⟩
    · simp only [Segmentation.Rule.Applies, Segmentation.Left.Holds, Segmentation.Right.Holds]
      exact ⟨⟨[], _, rfl, .one rfl⟩, rfl⟩
    · intro j r' hj hr' happ
      have hj0 : j = 0 := by omega
      subst hj0
      have hr : r' = ⟨"GB1", .sot Segmentation.nothing, .one Segmentation.anyCp, .brk⟩ := by
        first
          | exact (Option.some.inj hr'.symm)
          | (simp [Segmentation.rules] at hr'; exact hr'.symm)
      subst hr
      simp only [Segmentation.Rule.Applies, Segmentation.Left.Holds, Segmentation.nothing,
        List.take, List.map] at happ
      obtain ⟨hl, _⟩ := happ
      cases hl
      all_goals simp_all
  have hmem := (h "a" 1 (by first | decide | simp) (by first | decide | simp)).mpr (ht ▸ hb)
  first
    | exact absurd hmem (by decide)
    | simp [Segmentation.cutPoints] at hmem

-- "The two functions agree." `cutPoints []` is `[0]`, so a segmenter that returns no
-- clusters agrees with a boundary function that returns `[0]`. Passing them in the other
-- order does not type-check, which pins `BoundariesMatchCuts graphemes boundaries`.
theorem «BoundariesMatchCuts holds when boundaries is the cut points of graphemes on empty output» :
    Segmentation.BoundariesMatchCuts (fun _ => ([] : List String)) (fun _ => [0]) := by
  intro _
  rfl
