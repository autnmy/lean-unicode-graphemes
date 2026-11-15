import Segmentation

-- "`#guard` checks that `propsLookup` equals `Tables.props` on U+0000, U+0301 (Extend), U+200D
-- (ZWJ), U+094D (InCB Linker), U+0915 (InCB Consonant), U+1F1E6 (Regional Indicator), U+1F600
-- (Extended_Pictographic) and U+10FFFF"
-- Both sides are evaluated, so a wrong split point in the merged table shows up as a mismatch.
set_option maxRecDepth 20000 in
theorem «propsLookup_equals_props_on_listed_code_points» :
    ([0x0000, 0x0301, 0x200D, 0x094D, 0x0915, 0x1F1E6, 0x1F600, 0x10FFFF].all fun n =>
      decide (Segmentation.Tables.propsLookup (Char.ofNat n) =
        Segmentation.Tables.props (Char.ofNat n))) = true := by
  decide
