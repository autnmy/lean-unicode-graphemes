import Segmentation.ScanInvariants

open Segmentation

-- "three RI give `riOdd = true`, four give false"
theorem «scanStateOf: four regional indicators leave riOdd false» :
    (scanStateOf ({ gcb := .RI, extPict := false, incb := .None } : Props)
      [{ gcb := .RI, extPict := false, incb := .None },
       { gcb := .RI, extPict := false, incb := .None },
       { gcb := .RI, extPict := false, incb := .None }]).riOdd = false := by
  decide
