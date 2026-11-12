import Segmentation.ScanInvariants

open Segmentation

-- "one RI after a non-RI code point followed by an RI gives no boundary through GB13"
theorem «IsBoundary: no boundary inside an RI pair after a non-RI code point through GB13» :
    ¬ IsBoundary
      (fun c => if c = 'a'
        then ({ gcb := .Other, extPict := false, incb := .None } : Props)
        else { gcb := .RI, extPict := false, incb := .None })
      ['a', 'r', 's'] 2 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary
    (fun c => if c = 'a'
      then ({ gcb := .Other, extPict := false, incb := .None } : Props)
      else { gcb := .RI, extPict := false, incb := .None })
    'a' ['r', 's'] 1 (by decide)).mpr h
  revert hb
  decide
