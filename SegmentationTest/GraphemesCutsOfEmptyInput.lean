import Segmentation

-- "`Segmentation.boundaries : String → List Nat`, the cut positions counted in code points."
-- `cutPoints []` is `[0]`, so for H2' the boundary list of the empty text must be `[0]`, not `[]`,
-- and the empty text has no clusters.
theorem «cutsOf on empty input is [0], matching cutPoints of no clusters» :
    Segmentation.cutsOf (fun _ => { gcb := .Other, extPict := false, incb := .None }) [] = [0] ∧
      Segmentation.clustersOf (fun _ => { gcb := .Other, extPict := false, incb := .None }) [] = [] := by
  decide
