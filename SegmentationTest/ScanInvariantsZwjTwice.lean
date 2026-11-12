import Segmentation.ScanInvariants

open Segmentation

-- "ExtPict, ZWJ, ZWJ gives `zwjAfterPict = false`"
-- A second ZWJ is not GCB Extend, so it ends the pictographic run that GB11 reads.
theorem «scanStateOf: ExtPict, ZWJ, ZWJ leaves zwjAfterPict false» :
    (scanStateOf ({ gcb := .Other, extPict := true, incb := .None } : Props)
      [{ gcb := .ZWJ, extPict := false, incb := .None },
       { gcb := .ZWJ, extPict := false, incb := .None }]).zwjAfterPict = false := by
  decide
