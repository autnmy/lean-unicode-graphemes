import Segmentation.ScanInvariants

open Segmentation

-- "three RI give `riOdd = true`, four give false"
theorem «scanStateOf: three regional indicators leave riOdd true» :
    (scanStateOf ({ gcb := .RI, extPict := false, incb := .None } : Props)
      [{ gcb := .RI, extPict := false, incb := .None },
       { gcb := .RI, extPict := false, incb := .None }]).riOdd = true := by
  decide
