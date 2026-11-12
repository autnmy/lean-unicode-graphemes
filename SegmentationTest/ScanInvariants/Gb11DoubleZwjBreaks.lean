import Segmentation

-- GB11 needs ExtPict Extend* ZWJ right before the pictograph. In ExtPict, ZWJ, ZWJ, ExtPict
-- the second ZWJ follows a ZWJ, not that pattern, so GB11 fails and GB999 breaks at position 3.
theorem «GB11 does not join a pictograph after ZWJ ZWJ» :
    Segmentation.IsBoundary
      (fun c => if c = 'z' then ({ gcb := .ZWJ, extPict := false, incb := .None } : Segmentation.Props)
                else ({ gcb := .Other, extPict := true, incb := .None } : Segmentation.Props))
      ['p', 'z', 'z', 'p'] 3 :=
  (Segmentation.breaksBefore_iff_isBoundary
      (fun c => if c = 'z' then ({ gcb := .ZWJ, extPict := false, incb := .None } : Segmentation.Props)
                else ({ gcb := .Other, extPict := true, incb := .None } : Segmentation.Props))
      'p' ['z', 'z', 'p'] 2 (by decide)).mp (by decide)
