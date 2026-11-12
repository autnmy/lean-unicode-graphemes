import Segmentation

-- The first rule that applies decides: after CR, GB4 (index 3, break) comes before GB9
-- (index 8, no break before Extend), so CR then Extend has a boundary at position 1.
theorem «GB4 break after CR wins over the later GB9 no-break before Extend» :
    Segmentation.IsBoundary
      (fun c => if c = '\r' then ({ gcb := .CR, extPict := false, incb := .None } : Segmentation.Props)
                else ({ gcb := .Extend, extPict := false, incb := .Extend } : Segmentation.Props))
      ['\r', 'e'] 1 :=
  (Segmentation.breaksBefore_iff_isBoundary
      (fun c => if c = '\r' then ({ gcb := .CR, extPict := false, incb := .None } : Segmentation.Props)
                else ({ gcb := .Extend, extPict := false, incb := .Extend } : Segmentation.Props))
      '\r' ['e'] 0 (by decide)).mp (by decide)
