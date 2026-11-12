import Segmentation

-- GB13's left side needs the RI run to be preceded by a non-RI code point, so a ZWJ inside a
-- run starts a new count: RI, ZWJ, RI ends in a run of one (odd), and RI, ZWJ, RI, RI in a run
-- of two (even). A scan that keeps the old count across the ZWJ gets both wrong.
theorem «riOdd restarts its count after a ZWJ between regional indicators» :
    (Segmentation.scanStateOf
        ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props)
        [({ gcb := .ZWJ, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props)]).riOdd = true ∧
    (Segmentation.scanStateOf
        ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props)
        [({ gcb := .ZWJ, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props),
         ({ gcb := .RI, extPict := false, incb := .None } : Segmentation.Props)]).riOdd = false := by
  decide
