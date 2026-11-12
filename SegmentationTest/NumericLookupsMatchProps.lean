import Segmentation

open Segmentation in
set_option maxRecDepth 20000 in
theorem «incbOf and extPictOf give the file values by number for U+094D, U+00A9, U+0041 and U+10FFFF» :
    (Segmentation.Tables.incbOf 0x094D, Segmentation.Tables.extPictOf 0x00A9,
     Segmentation.Tables.extPictOf 0x0041, Segmentation.Tables.incbOf 0x10FFFF)
      = (InCB.Linker, true, false, InCB.None) := by
  decide
