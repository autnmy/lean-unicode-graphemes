import Segmentation

-- "`Segmentation.Tables.propsLookup c = Segmentation.Tables.props c` is proved for every `Char c`
-- by `Tables.propsLookup_eq_props`, not sampled."
-- The ascription fails to elaborate if the theorem is renamed, takes a hypothesis, or is stated
-- over `Nat` or a sample of characters.
theorem «propsLookup_eq_props_holds_for_every_char_without_hypothesis» : True := by
  have _x : ∀ c : Char, Segmentation.Tables.propsLookup c = Segmentation.Tables.props c :=
    Segmentation.Tables.propsLookup_eq_props
  trivial
