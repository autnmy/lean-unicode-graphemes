import Segmentation

open Segmentation

def scanInvGB13Props (c : Char) : Props :=
  if c = 'a' then { gcb := .Other, extPict := false, incb := .None }
  else { gcb := .RI, extPict := false, incb := .None }

-- "one RI after a non-RI code point followed by an RI gives no boundary through GB13"
theorem «RI after a non-RI followed by an RI has no boundary through GB13» :
    ¬ IsBoundary scanInvGB13Props ['a', 'r', 's'] 2 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary scanInvGB13Props 'a' ['r', 's'] 1 (by decide)).mpr h
  exact absurd hb (by decide)
