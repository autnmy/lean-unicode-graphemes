import Segmentation

-- `cutPoints []` is `[0]`, so the empty text must have no clusters for H2' to hold.
theorem «graphemes of the empty string is the empty list» :
    (Segmentation.graphemes "" == ([] : List String)) = true := by
  decide
