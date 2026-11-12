import Segmentation

open Segmentation in
set_option maxRecDepth 20000 in
theorem «incbOf and extPictOf agree with props by number for U+094D and U+00A9» :
    (Segmentation.Tables.incbOf 0x094D, Segmentation.Tables.extPictOf 0x00A9,
     Segmentation.Tables.extPictOf 0x0041, Segmentation.Tables.incbOf 0x10FFFF)
      = (InCB.Linker, true, false, InCB.None) := by
  decide
