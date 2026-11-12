import Segmentation

open Segmentation

def scanInvGB11Props (c : Char) : Props :=
  if c = 'z' then { gcb := .ZWJ, extPict := false, incb := .None }
  else { gcb := .Other, extPict := true, incb := .None }

-- "ExtPict, ZWJ, ExtPict (GCB Other on the pictographs, InCB None) gives `breaksBefore = false` and no boundary at position 2 through GB11"
theorem «ExtPict ZWJ ExtPict has no boundary at position 2 through GB11» :
    breaksBefore (scanStateOf (scanInvGB11Props 'p') [scanInvGB11Props 'z'])
        (scanInvGB11Props 'q') = false ∧
      ¬ IsBoundary scanInvGB11Props ['p', 'z', 'q'] 2 := by
  refine ⟨by decide, fun h => ?_⟩
  have hb := (breaksBefore_iff_isBoundary scanInvGB11Props 'p' ['z', 'q'] 1 (by decide)).mpr h
  exact absurd hb (by decide)
