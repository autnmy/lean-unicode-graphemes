import Segmentation

-- "Prove that the clusters put back together are the input, and that no cluster is empty."
-- The ascription pins the exact committed statement, so a theorem about a weaker or toy
-- statement does not elaborate here.
theorem «graphemes_ne_empty proves H1b for graphemes» :
    Segmentation.H1b Segmentation.graphemes :=
  Segmentation.graphemes_ne_empty
