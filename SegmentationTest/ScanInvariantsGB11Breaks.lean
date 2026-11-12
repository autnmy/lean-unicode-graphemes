import Segmentation.ScanInvariants

open Segmentation

-- "ExtPict, ZWJ, ExtPict (GCB Other on the pictographs, InCB None) gives `breaksBefore = false`"
theorem «breaksBefore: ExtPict, ZWJ then ExtPict does not break» :
    breaksBefore
      (scanStateOf ({ gcb := .Other, extPict := true, incb := .None } : Props)
        [{ gcb := .ZWJ, extPict := false, incb := .None }])
      { gcb := .Other, extPict := true, incb := .None } = false := by
  decide
