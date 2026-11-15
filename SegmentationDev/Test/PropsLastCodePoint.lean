import Segmentation

open Segmentation in
-- The top of the range is unlisted in every file, so each property takes its default.
set_option maxRecDepth 20000 in
theorem props_10FFFF_is_other_not_pictographic_incb_none :
    Segmentation.Tables.props (Char.ofNat 0x10FFFF) = { gcb := GCB.other, extPict := false, incb := InCB.none } := by
  decide
