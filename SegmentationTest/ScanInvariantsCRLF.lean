import Segmentation.ScanInvariants

open Segmentation

-- "CR then LF gives no boundary at position 1"
theorem «IsBoundary: no boundary between CR and LF» :
    ¬ IsBoundary
      (fun c => if c = '\r'
        then ({ gcb := .CR, extPict := false, incb := .None } : Props)
        else { gcb := .LF, extPict := false, incb := .None })
      ['\r', '\n'] 1 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary
    (fun c => if c = '\r'
      then ({ gcb := .CR, extPict := false, incb := .None } : Props)
      else { gcb := .LF, extPict := false, incb := .None })
    '\r' ['\n'] 0 (by decide)).mpr h
  revert hb
  decide
