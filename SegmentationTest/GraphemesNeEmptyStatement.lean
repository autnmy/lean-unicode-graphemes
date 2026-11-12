import Segmentation

-- "Prove that the clusters put back together are the input, and that no cluster is empty."
-- The type ascription pins the theorem to the committed statement `H1b` applied to the real
-- segmenter.
theorem «graphemes_ne_empty is stated as H1b applied to graphemes» :
    Segmentation.H1b Segmentation.graphemes :=
  Segmentation.graphemes_ne_empty
