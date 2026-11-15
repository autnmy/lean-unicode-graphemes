import Segmentation

open Segmentation in
-- "`#guard` checks that `propsLookup` equals `Tables.props` on U+0000, U+0301 (Extend), U+200D
-- (ZWJ), U+094D (InCB Linker), U+0915 (InCB Consonant), U+1F1E6 (Regional Indicator), U+1F600
-- (Extended_Pictographic) and U+10FFFF"
-- Astral code points are written as numbers, as the other tests in this directory do.
set_option maxRecDepth 20000 in
theorem «propsLookup_agrees_with_props_on_each_listed_code_point_by_number» :
    ([0x0000, 0x0301, 0x200D, 0x094D, 0x0915, 0x1F1E6, 0x1F600, 0x10FFFF].all
      (fun n => Segmentation.Tables.propsLookup (Char.ofNat n) == Segmentation.Tables.props (Char.ofNat n)))
      = true := by
  decide
