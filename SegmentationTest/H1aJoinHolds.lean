import Segmentation

-- "H1, partition: the clusters put back together are the input, and none is empty."
-- A segmenter that returns the whole text as one cluster joins back to the input exactly.
theorem «H1a holds for a segmenter whose clusters join back to the input» :
    Segmentation.H1a (fun s => [s]) := by
  intro s
  first
    | simp [String.join]
    | rfl
