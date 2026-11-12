import Segmentation.ScanInvariants

open Segmentation

-- "ExtPict, ZWJ, ExtPict (GCB Other on the pictographs, InCB None) gives `breaksBefore = false` and no boundary at position 2 through GB11"
-- IsBoundary is not decidable, so the boundary claim goes through the equivalence.
theorem «IsBoundary: no boundary at position 2 of ExtPict, ZWJ, ExtPict through GB11» :
    ¬ IsBoundary
      (fun c => if c = 'z'
        then ({ gcb := .ZWJ, extPict := false, incb := .None } : Props)
        else { gcb := .Other, extPict := true, incb := .None })
      ['a', 'z', 'b'] 2 := by
  intro h
  have hb := (breaksBefore_iff_isBoundary
    (fun c => if c = 'z'
      then ({ gcb := .ZWJ, extPict := false, incb := .None } : Props)
      else { gcb := .Other, extPict := true, incb := .None })
    'a' ['z', 'b'] 1 (by decide)).mpr h
  revert hb
  decide
