import SegmentationDev.Gate.Axioms
import Segmentation

-- "`#assert_axioms` on the theorem passes with only `propext`, `Classical.choice`, `Quot.sound`;
-- no `sorry`, `native_decide`, `implemented_by`, `extern` or `partial` is used."
-- The theorem is restated here so the check below runs on a named test that carries the
-- library theorem's whole axiom footprint.
theorem «propsLookup_eq_props rests only on propext, Classical.choice and Quot.sound» :
    ∀ c : Char, Segmentation.Tables.propsLookup c = Segmentation.Tables.props c :=
  Segmentation.Tables.propsLookup_eq_props

#assert_axioms Segmentation.Tables.propsLookup_eq_props
  «propsLookup_eq_props rests only on propext, Classical.choice and Quot.sound»
