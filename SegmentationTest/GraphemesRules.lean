import Lean
import Segmentation

/-!
Checks of the cut theorems in `Segmentation.Cuts` and `Segmentation.Rules`: the segmenter cuts
exactly where UAX #29 says (`H2`), `boundaries` gives the cut points of `graphemes` (`H2'`), and
the cut positions of the list core are characterised by the one-pass scan state for any
property lookup (`mem_cutsOf`).
-/

-- The ascriptions name the committed `H2` and `H2'` terms, not unfolded copies, so a theorem
-- that is missing, renamed, or proved against a restated or weaker local statement fails here.
open Segmentation in
theorem «graphemes_rules proves the committed H2 statement at Tables.props and graphemes» :
    Segmentation.H2 Tables.props Segmentation.graphemes :=
  (Segmentation.graphemes_rules : Segmentation.H2 Tables.props Segmentation.graphemes)

theorem «boundaries_agree proves the committed H2' statement at graphemes and boundaries» :
    Segmentation.H2' Segmentation.graphemes Segmentation.boundaries :=
  (Segmentation.boundaries_agree : Segmentation.H2' Segmentation.graphemes Segmentation.boundaries)

-- The type quantifies over every `props`, so a lemma proved only at `Tables.props` fails here.
open Segmentation in
theorem «mem_cutsOf holds for every props with its stated type» :
    ∀ (props : Char → Props) (c : Char) (cs : List Char) (i : Nat),
      i ∈ cutsOf props (c :: cs) ↔ i = 0 ∨ i = cs.length + 1 ∨
        ∃ (j : Nat) (h : j < cs.length), i = j + 1 ∧
          breaksBefore (scanStateOf (props c) ((cs.take j).map props)) (props cs[j]) = true :=
  Segmentation.mem_cutsOf

-- `#print axioms` only prints, so this reads the same axiom list and fails on anything beyond
-- `propext`, `Classical.choice` and `Quot.sound`. A proof that hides a `sorry` anywhere in its
-- lemmas depends on `sorryAx`, which is not in the allowed list.
open Lean in
theorem «graphemes_rules and boundaries_agree use no sorry and no axiom beyond propext, Classical.choice and Quot.sound» :
    True := by
  run_tac do
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let names := [``Segmentation.graphemes_rules, ``Segmentation.boundaries_agree]
    for name in names do
      let used ← collectAxioms name
      for ax in used do
        unless allowed.contains ax do
          throwError m!"{name} depends on the disallowed axiom {ax}"
  trivial
