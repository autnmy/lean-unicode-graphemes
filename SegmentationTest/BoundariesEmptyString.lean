import Segmentation

-- `cutPoints []` is `[0]`, and H2' asks `boundaries s = cutPoints (graphemes s)`.
theorem «boundaries of the empty string is the single cut 0» :
    (Segmentation.boundaries "" == [0]) = true := by
  decide
