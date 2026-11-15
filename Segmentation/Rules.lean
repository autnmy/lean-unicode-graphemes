import Segmentation.Statements
import Segmentation.Tables
import Segmentation.Graphemes
import Segmentation.ScanInvariants
import Segmentation.Cuts

/-!
# The clusters cut exactly where UAX #29 says

`graphemes_rules` proves `CutsMatchRules`: at every position of a non-empty string, `graphemes`
cuts exactly where the first rule of UAX #29 that applies says ÷. `boundaries_agree` turns the
cut points of `graphemes` into `cutsOf`, and `mem_cutsOf` lists those as the two ends of the text
and each position inside it where `breaksBefore` says ÷. The ends are boundaries by
`isBoundary_zero` and `isBoundary_length`, and `breaksBefore_iff_isBoundary` matches the verdict
at each position inside.
-/

namespace Segmentation

/-- `CutsMatchRules` for `graphemes`: on a non-empty string, a position is a cut point of
`graphemes` exactly when UAX #29 puts a boundary there. -/
theorem graphemes_rules : CutsMatchRules Tables.props graphemes := by
  intro s i hs hi
  rw [← boundaries_agree s]
  show i ∈ cutsOf Tables.props s.toList ↔ IsBoundary Tables.props s.toList i
  rw [← String.length_toList] at hi
  cases hcs : s.toList with
  | nil => exact absurd (String.toList_eq_nil_iff.mp hcs) hs
  | cons c cs =>
    rw [hcs] at hi
    simp only [List.length_cons] at hi
    rw [mem_cutsOf]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, rfl, hb⟩)
      · exact isBoundary_zero Tables.props (c :: cs) (List.cons_ne_nil c cs)
      · exact isBoundary_length Tables.props (c :: cs) (List.cons_ne_nil c cs)
      · exact (breaksBefore_iff_isBoundary Tables.props c cs j hj).mp hb
    · intro hb
      cases i with
      | zero => exact Or.inl rfl
      | succ j =>
        if hj : j < cs.length then
          exact Or.inr (Or.inr
            ⟨j, hj, rfl, (breaksBefore_iff_isBoundary Tables.props c cs j hj).mpr hb⟩)
        else
          exact Or.inr (Or.inl (by omega))

end Segmentation
