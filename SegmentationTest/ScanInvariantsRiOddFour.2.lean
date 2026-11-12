import Segmentation

open Segmentation

def scanInvRiOddFourRI : Props := { gcb := .RI, extPict := false, incb := .None }

-- "three RI give `riOdd = true`, four give false"
theorem «four regional indicators leave riOdd false» :
    (scanStateOf scanInvRiOddFourRI
      [scanInvRiOddFourRI, scanInvRiOddFourRI, scanInvRiOddFourRI]).riOdd = false := by
  decide
