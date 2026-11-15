import Segmentation

-- "ASCII bytes get properties from a small pure `asciiProps`, proved equal to `Tables.props` for
-- every code point below 128 by `decide`."
-- The ascription fails if the theorem covers fewer code points or compares with another lookup.
theorem «asciiProps_eq_props_type_covers_every_code_point_below_128» : True := by
  have _x : ∀ n < 128, Segmentation.asciiProps n = Segmentation.Tables.props (Char.ofNat n) :=
    Segmentation.asciiProps_eq_props
  trivial
