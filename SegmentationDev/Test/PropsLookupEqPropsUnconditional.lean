import Segmentation

-- "`Segmentation.Tables.propsLookup c = Segmentation.Tables.props c` is proved for every
-- `Char c` by `Tables.propsLookup_eq_props`, not sampled."
-- A statement with a sortedness premise, a bound on the code point, or a `Nat` argument does
-- not elaborate against this type.
theorem «propsLookup_eq_props holds for every Char with no hypothesis» : True := by
  have _x : ∀ c : Char, Segmentation.Tables.propsLookup c = Segmentation.Tables.props c :=
    Segmentation.Tables.propsLookup_eq_props
  trivial
