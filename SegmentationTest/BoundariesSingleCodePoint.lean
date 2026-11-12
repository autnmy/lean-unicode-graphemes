import Segmentation

-- The cut list includes both ends of the text: 0 and the length in code points.
set_option maxRecDepth 20000 in
theorem «boundaries of a one code point string is 0 and 1» :
    (Segmentation.boundaries "a" == [0, 1]) = true := by
  decide
