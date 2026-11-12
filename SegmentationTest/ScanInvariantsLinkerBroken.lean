import Segmentation.ScanInvariants

open Segmentation

-- "Linker then an InCB None code point gives `linkerTail = false`"
theorem «scanStateOf: Linker then an InCB None code point leaves linkerTail false» :
    (scanStateOf ({ gcb := .Extend, extPict := false, incb := .Linker } : Props)
      [{ gcb := .Other, extPict := false, incb := .None }]).linkerTail = false := by
  decide
