import Segmentation

-- "`#guard` checks that `propsLookup` equals `Tables.props` on U+0000, U+0301 (Extend), U+200D
-- (ZWJ), U+094D (InCB Linker), U+0915 (InCB Consonant), U+1F1E6 (Regional Indicator), U+1F600
-- (Extended_Pictographic) and U+10FFFF"
set_option maxRecDepth 20000 in
theorem «propsLookup equals props on the eight listed code points» :
    ([0x0000, 0x0301, 0x200D, 0x094D, 0x0915, 0x1F1E6, 0x1F600, 0x10FFFF].map
        (fun n => Segmentation.Tables.propsLookup (Char.ofNat n))) =
      ([0x0000, 0x0301, 0x200D, 0x094D, 0x0915, 0x1F1E6, 0x1F600, 0x10FFFF].map
        (fun n => Segmentation.Tables.props (Char.ofNat n))) := by
  decide
