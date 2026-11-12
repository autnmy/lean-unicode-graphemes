import Segmentation

-- GraphemeBreakProperty.txt lists no range covering U+D800, so it takes the file's default, Other.
set_option maxRecDepth 20000 in
theorem «gcbOf looks up surrogates and line breaks by number» :
    (Segmentation.Tables.gcbOf 0xD800 == Segmentation.GCB.Other &&
     Segmentation.Tables.gcbOf 0x000D == Segmentation.GCB.CR &&
     Segmentation.Tables.gcbOf 0x000A == Segmentation.GCB.LF &&
     Segmentation.Tables.gcbOf 0xAC00 == Segmentation.GCB.LV &&
     Segmentation.Tables.gcbOf 0xAC01 == Segmentation.GCB.LVT) = true := by
  decide
