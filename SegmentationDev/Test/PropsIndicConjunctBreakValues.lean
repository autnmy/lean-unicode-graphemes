import Segmentation

open Segmentation in
-- Expected values are written by hand from the `InCB` lines of DerivedCoreProperties.txt;
-- U+0041 is unlisted there and so takes the default.
set_option maxRecDepth 20000 in
theorem props_gives_file_incb_value_for_each_value :
    (['\u0915', '\u0300', '\u094D', 'A'].map fun c => (Segmentation.Tables.props c).incb)
      = [InCB.consonant, InCB.extend, InCB.linker, InCB.none] := by
  decide
