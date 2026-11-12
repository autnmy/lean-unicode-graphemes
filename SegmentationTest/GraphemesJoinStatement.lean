import Segmentation

-- "Prove that the clusters put back together are the input, and that no cluster is empty."
-- The type ascription pins the theorem to the committed statement `H1a` applied to the real
-- segmenter, so a theorem about a weaker statement or a different segmenter fails here.
theorem «graphemes_join is stated as H1a applied to graphemes» :
    Segmentation.H1a Segmentation.graphemes :=
  Segmentation.graphemes_join
