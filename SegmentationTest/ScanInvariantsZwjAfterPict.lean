import Segmentation

open Segmentation

def scanInvZwjPict : Props := { gcb := .Other, extPict := true, incb := .None }
def scanInvZwjZwj : Props := { gcb := .ZWJ, extPict := false, incb := .None }

-- "ExtPict, ZWJ, ZWJ gives `zwjAfterPict = false`"
-- The two-element case pins that the flag is not simply always false.
theorem «ExtPict ZWJ ZWJ leaves zwjAfterPict false but ExtPict ZWJ sets it» :
    (scanStateOf scanInvZwjPict [scanInvZwjZwj, scanInvZwjZwj]).zwjAfterPict = false ∧
    (scanStateOf scanInvZwjPict [scanInvZwjZwj]).zwjAfterPict = true := by
  decide
