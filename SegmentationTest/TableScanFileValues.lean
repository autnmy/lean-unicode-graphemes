import Segmentation

-- The scan is evaluated directly, then carried back to the lookups through the corollaries, so
-- both the reference and the theorems must agree with the Unicode data values.
open Segmentation Segmentation.Tables in
set_option maxRecDepth 20000 in
theorem «the linear scan of the committed tables gives the file values for U+094D, U+00A9 and U+10FFFF» :
    incbOf 0x094D = InCB.Linker ∧ extPictOf 0x00A9 = true ∧ extPictOf 0x0041 = false ∧
      incbOf 0x10FFFF = InCB.None := by
  rw [incbOf_eq_scan, incbOf_eq_scan, extPictOf_eq_scan, extPictOf_eq_scan]
  decide
