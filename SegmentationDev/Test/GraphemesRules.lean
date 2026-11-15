import Segmentation

/-!
Checks of the cut theorems in `Segmentation.Cuts` and `Segmentation.Rules`: the segmenter cuts
exactly where UAX #29 says (`CutsMatchRules`), `boundaries` gives the cut points of `graphemes`
(`BoundariesMatchCuts`), and the cut positions of the list core are characterised by the
one-pass scan state for any property lookup (`mem_cutsOf`).
-/

-- The ascriptions name the committed `CutsMatchRules` and `BoundariesMatchCuts` terms, not
-- unfolded copies, so a theorem that is missing, renamed, or proved against a restated or weaker
-- local statement fails here.
open Segmentation in
theorem «graphemes_rules proves the committed CutsMatchRules at Tables.props and graphemes» :
    Segmentation.CutsMatchRules Tables.props Segmentation.graphemes :=
  (Segmentation.graphemes_rules : Segmentation.CutsMatchRules Tables.props Segmentation.graphemes)

theorem «boundaries_agree proves the committed BoundariesMatchCuts at graphemes and boundaries» :
    Segmentation.BoundariesMatchCuts Segmentation.graphemes Segmentation.boundaries :=
  (Segmentation.boundaries_agree :
    Segmentation.BoundariesMatchCuts Segmentation.graphemes Segmentation.boundaries)

-- The type quantifies over every `props`, so a lemma proved only at `Tables.props` fails here.
open Segmentation in
theorem «mem_cutsOf holds for every props with its stated type» :
    ∀ (props : Char → Props) (c : Char) (cs : List Char) (i : Nat),
      i ∈ cutsOf props (c :: cs) ↔ i = 0 ∨ i = cs.length + 1 ∨
        ∃ (j : Nat) (h : j < cs.length), i = j + 1 ∧
          breaksBefore (scanStateOf (props c) ((cs.take j).map props)) (props cs[j]) = true :=
  Segmentation.mem_cutsOf

-- The axiom check for `graphemes_rules` and `boundaries_agree` is in
-- `SegmentationDev.Test.HeadlineAxioms`, with the other headline theorems.
