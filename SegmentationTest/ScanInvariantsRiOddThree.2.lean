import Segmentation

open Segmentation

def scanInvRiOddThreeRI : Props := { gcb := .RI, extPict := false, incb := .None }

-- "three RI give `riOdd = true`, four give false"
theorem «three regional indicators leave riOdd true» :
    (scanStateOf scanInvRiOddThreeRI [scanInvRiOddThreeRI, scanInvRiOddThreeRI]).riOdd = true := by
  decide
