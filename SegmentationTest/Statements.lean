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
      r.left.Holds [{ gcb := GCB.Extend, extPict := false, incb := InCB.Linker }] ∧
      r.right.Holds [{ gcb := GCB.Other, extPict := false, incb := InCB.Consonant }] := by
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · exact (⟨[], [{ gcb := GCB.Extend, extPict := false, incb := InCB.Linker }] ++ [], rfl,
      Pat.Matches.seq (Pat.Matches.one rfl) Pat.Matches.starNil⟩ :
      ∃ a b, [({ gcb := GCB.Extend, extPict := false, incb := InCB.Linker } : Props)] = a ++ b ∧
        Pat.Matches (.seq (.one (incbIs .Linker)) (.star (incbIs .Extend))) b)
  · exact (⟨{ gcb := GCB.Other, extPict := false, incb := InCB.Consonant }, [], rfl, rfl⟩ :
      ∃ x rest, [({ gcb := GCB.Other, extPict := false, incb := InCB.Consonant } : Props)] =
        x :: rest ∧ incbIs .Consonant x = true)

-- H1a and H1b mention only `graphemes`, so they must not also demand the property lookup
-- or the boundary function; a stray parameter would make these ascriptions fail.
theorem «H1a depends on the segmenter alone» : True := by
  have _h1a : (String → List String) → Prop := Segmentation.H1a
  trivial

theorem «H1b is stated over the segmenter alone» : True := by
  have _h1b : (String → List String) → Prop := Segmentation.H1b
  trivial

-- Later proofs apply `H2 props graphemes` and `H2' graphemes boundaries`. If the section
-- variables were declared in another order, these ascriptions would not type-check.
theorem «H2 takes the property lookup first and the segmenter second» : True := by
  have _h2 : (Char → Segmentation.Props) → (String → List String) → Prop := Segmentation.H2
  trivial

theorem «H2' takes the segmenter first and the boundary function second» : True := by
  have _h2' : (String → List String) → (String → List Nat) → Prop := Segmentation.H2'
  trivial

-- "H1, partition: the clusters put back together are the input, and none is empty."
-- A segmenter that returns the whole text as one cluster joins back to the input exactly.
theorem «H1a holds for a segmenter whose clusters join back to the input» :
    Segmentation.H1a (fun s => [s]) := by
  intro s
  first
    | simp [String.join]
    | rfl

-- A segmenter that returns no clusters loses the text "a", so H1a must not hold for it.
theorem «H1a rejects a segmenter that drops the text» :
    ¬ Segmentation.H1a (fun _ => []) := by
  intro h
  have hjoin := h "a"
  first
    | exact absurd hjoin (by decide)
    | simp [String.join] at hjoin

theorem «H1b rejects a segmenter that returns an empty cluster» :
    ¬ Segmentation.H1b (fun _ => [""]) := by
  intro h
  exact h "" "" (by simp) rfl

-- "H2, the rules: at every position of a non-empty text, ends included, a cut falls exactly where
-- UAX #29 puts a boundary. The ends make GB1 and GB2 live in the proof."
-- For the text "a", GB2 puts a boundary at position 1 (the end). A segmenter returning no
-- clusters has cut points [0] only, so H2 must not hold for it.
theorem «H2 rejects a segmenter that leaves out the end-of-text cut» :
    ¬ Segmentation.H2 (fun _ => ⟨.Other, false, .None⟩) (fun _ => []) := by
  intro h
  have ht : "a".toList = ['a'] := by first | rfl | decide | simp
  have hb : Segmentation.IsBoundary (fun _ => ⟨.Other, false, .None⟩) ['a'] 1 := by
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

-- "H2', the two functions agree." `cutPoints []` is `[0]`, so a segmenter that returns no
-- clusters agrees with a boundary function that returns `[0]`. Passing them in the other
-- order does not type-check, which pins `H2' graphemes boundaries`.
theorem «H2' holds when boundaries is the cut points of graphemes on empty output» :
    Segmentation.H2' (fun _ => ([] : List String)) (fun _ => [0]) := by
  intro _
  rfl
