import Segmentation

-- "Prove that the clusters put back together are the input, and that no cluster is empty."
-- The ascription pins the exact committed statement, so a theorem about a weaker or toy
-- statement does not elaborate here.
theorem «graphemes_join proves H1a for graphemes» :
    Segmentation.H1a Segmentation.graphemes :=
  Segmentation.graphemes_join
