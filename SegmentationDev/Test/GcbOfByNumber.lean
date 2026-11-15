import Segmentation

open Segmentation in
-- A Char cannot hold a surrogate, so the numeric lookup is the only way to read them.
-- GraphemeBreakProperty.txt lists no range covering U+D800..U+DFFF, so they take its
-- `@missing` default, Other.
set_option maxRecDepth 20000 in
theorem «gcbOf gives surrogates U+D800 and U+DFFF the file default Other and keeps U+1F1E6 as RI» :
    ([0xD800, 0xDFFF, 0x1F1E6].map Segmentation.Tables.gcbOf) =
      [GCB.other, GCB.other, GCB.regionalIndicator] := by
  decide
