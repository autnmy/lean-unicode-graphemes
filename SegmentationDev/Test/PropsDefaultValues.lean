import Segmentation

open Segmentation in
-- The combined table's default must be the three source lookups' defaults, so code points that
-- no source range covers keep the values `props` gives them.
theorem «propsDefault is Other, not pictographic, InCB None» :
    Segmentation.Tables.propsDefault = { gcb := GCB.other, extPict := false, incb := InCB.none } := by
  decide
