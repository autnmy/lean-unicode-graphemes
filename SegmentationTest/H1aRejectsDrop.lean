import Segmentation

-- "H1, partition: the clusters put back together are the input, and none is empty."
-- A segmenter that returns no clusters loses the text "a", so H1a must not hold for it.
theorem «H1a rejects a segmenter that drops the text» :
    ¬ Segmentation.H1a (fun _ => []) := by
  intro h
  have hjoin := h "a"
  first
    | exact absurd hjoin (by decide)
    | simp [String.join] at hjoin
