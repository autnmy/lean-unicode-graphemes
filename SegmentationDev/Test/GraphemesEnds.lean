import Segmentation

-- `cutPoints []` is `[0]`, so the empty text must have no clusters for BoundariesMatchCuts to hold.
theorem «graphemes of the empty string is the empty list» :
    (Segmentation.graphemes "" == ([] : List String)) = true := by
  decide

-- `cutPoints []` is `[0]`, and BoundariesMatchCuts asks `boundaries s = cutPoints (graphemes s)`.
theorem «boundaries of the empty string is the single cut 0» :
    (Segmentation.boundaries "" == [0]) = true := by
  decide

-- "`Segmentation.boundaries : String → List Nat`, the cut positions counted in code points."
-- `cutPoints []` is `[0]`, so for BoundariesMatchCuts the boundary list of the empty text must be
-- `[0]`, not `[]`, and the empty text has no clusters.
theorem «cutsOf on empty input is [0], matching cutPoints of no clusters» :
    Segmentation.cutsOf (fun _ => { gcb := .other, extPict := false, incb := .none }) [] = [0] ∧
      Segmentation.clustersOf (fun _ => { gcb := .other, extPict := false, incb := .none }) [] = [] := by
  decide

-- GB1 and GB2 put a cut at both ends of the text, so one code point is one cluster.
set_option maxRecDepth 20000 in
theorem «graphemes of a one code point string is that string» :
    (Segmentation.graphemes "a" == ["a"]) = true := by
  decide

-- The cut list includes both ends of the text: 0 and the length in code points.
set_option maxRecDepth 20000 in
theorem «boundaries of a one code point string is 0 and 1» :
    (Segmentation.boundaries "a" == [0, 1]) = true := by
  decide
