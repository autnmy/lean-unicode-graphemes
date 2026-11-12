import Segmentation

-- GB11's left side is ExtPict Extend* ZWJ: ExtPict, Extend, Extend, ZWJ matches it, and
-- ExtPict, Other, ZWJ does not, because the Other code point breaks the Extend run.
theorem «zwjAfterPict crosses an Extend run but not an Other code point» :
    (Segmentation.scanStateOf
        ({ gcb := .Other, extPict := true, incb := .None } : Segmentation.Props)
        [({ gcb := .Extend, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .Extend, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .ZWJ, extPict := false, incb := .None } : Segmentation.Props)]).zwjAfterPict = true ∧
    (Segmentation.scanStateOf
        ({ gcb := .Other, extPict := true, incb := .None } : Segmentation.Props)
        [({ gcb := .Other, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .ZWJ, extPict := false, incb := .None } : Segmentation.Props)]).zwjAfterPict = false := by
  decide
