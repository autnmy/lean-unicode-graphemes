import Segmentation

open Segmentation in
-- Each listed code point carries the property the issue names beside it, read through the one
-- combined lookup, so an equality with `props` cannot pass only because both sides give the
-- default.
set_option maxRecDepth 20000 in
theorem «propsLookup gives the named property on the listed code points» :
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0301)).gcb = GCB.extend ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x200D)).gcb = GCB.zwj ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x094D)).incb = InCB.linker ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0915)).incb = InCB.consonant ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x1F1E6)).gcb = GCB.regionalIndicator ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x1F600)).extPict = true ∧
    Segmentation.Tables.propsLookup (Char.ofNat 0x10FFFF) =
      { gcb := GCB.other, extPict := false, incb := InCB.none } := by
  decide
