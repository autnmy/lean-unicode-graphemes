import Segmentation

-- GB1 and GB2 put a cut at both ends of the text, so one code point is one cluster.
set_option maxRecDepth 20000 in
theorem «graphemes of a one code point string is that string» :
    (Segmentation.graphemes "a" == ["a"]) = true := by
  decide
