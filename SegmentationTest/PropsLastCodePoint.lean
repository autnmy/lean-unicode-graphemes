import Segmentation

open Segmentation in
-- The top of the range is unlisted in every file, so each property takes its default.
set_option maxRecDepth 20000 in
theorem «props of the last code point U+10FFFF is Other, not pictographic, InCB None» :
    Segmentation.Tables.props (Char.ofNat 0x10FFFF) = { gcb := GCB.Other, extPict := false, incb := InCB.None } := by
  decide
