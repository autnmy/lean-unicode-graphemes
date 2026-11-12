import Segmentation

-- "one RI after a non-RI code point followed by an RI gives no boundary through GB13."
theorem «GB13 joins one regional indicator after a non-RI code point to the next» :
    ¬ Segmentation.IsBoundary
      (fun c => if c = 'r' then ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props)
                else ({ gcb := .Other, extPict := false, incb := .None } : Segmentation.Props))
      ['x', 'r', 'r'] 2 := fun h =>
  absurd
    ((Segmentation.breaksBefore_iff_isBoundary
        (fun c => if c = 'r' then ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props)
                  else ({ gcb := .Other, extPict := false, incb := .None } : Segmentation.Props))
        'x' ['r', 'r'] 1 (by decide)).mpr h)
    (by decide)
