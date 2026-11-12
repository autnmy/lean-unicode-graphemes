import Segmentation

-- No cluster is empty: in particular the empty string never appears among the clusters of a
-- text made of several clusters.
theorem «graphemes_ne_empty rules out an empty first cluster» :
    "" ∉ Segmentation.graphemes "e\u0301\r\nx" :=
  fun h => Segmentation.graphemes_ne_empty "e\u0301\r\nx" "" h rfl
