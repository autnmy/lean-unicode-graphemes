import Segmentation

open Segmentation in
-- The listed code points carry the properties the issue names beside them: U+0301 (Extend),
-- U+200D (ZWJ), U+094D (InCB Linker), U+0915 (InCB Consonant), U+1F1E6 (Regional Indicator),
-- U+1F600 (Extended_Pictographic). Reading them as non-default values means an equality with
-- `props` cannot pass only because both sides fell back to the defaults.
set_option maxRecDepth 20000 in
theorem «propsLookup_reads_named_properties_of_listed_code_points» :
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0301)).gcb = GCB.extend ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x200D)).gcb = GCB.zwj ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x094D)).incb = InCB.linker ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0915)).incb = InCB.consonant ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x1F1E6)).gcb = GCB.regionalIndicator ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x1F600)).extPict = true ∧
    Segmentation.Tables.propsLookup (Char.ofNat 0x10FFFF) =
      { gcb := GCB.other, extPict := false, incb := InCB.none } ∧
    (Segmentation.Tables.propsLookup (Char.ofNat 0x0000)).gcb = GCB.control := by
  decide
