import Segmentation

open Segmentation

def scanInvCRLFProps (c : Char) : Props :=
  if c = '\r' then { gcb := .CR, extPict := false, incb := .None }
  else { gcb := .LF, extPict := false, incb := .None }

-- "CR then LF gives no boundary at position 1"
theorem «CR then LF has no boundary at position 1» :
    ¬ IsBoundary scanInvCRLFProps ['\r', '\n'] 1 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary scanInvCRLFProps '\r' ['\n'] 0 (by decide)).mpr h
  exact absurd hb (by decide)
