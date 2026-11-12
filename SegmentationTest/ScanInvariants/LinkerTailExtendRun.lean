import Segmentation

-- GB9c's left side is InCB Linker then InCB Extend*: Linker, Extend, Extend matches it, and
-- Linker, Extend, None, Extend does not, because the None code point ends the run.
theorem «linkerTail survives InCB Extend and is cleared by InCB None» :
    (Segmentation.scanStateOf
        ({ gcb := .Extend, extPict := false, incb := .Linker } : Segmentation.Props)
        [({ gcb := .Extend, extPict := false, incb := .Extend } : Segmentation.Props),
         ({ gcb := .Extend, extPict := false, incb := .Extend } : Segmentation.Props)]).linkerTail = true ∧
    (Segmentation.scanStateOf
        ({ gcb := .Extend, extPict := false, incb := .Linker } : Segmentation.Props)
        [({ gcb := .Extend, extPict := false, incb := .Extend } : Segmentation.Props),
         ({ gcb := .Other, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .Extend, extPict := false, incb := .Extend } : Segmentation.Props)]).linkerTail = false := by
  decide
