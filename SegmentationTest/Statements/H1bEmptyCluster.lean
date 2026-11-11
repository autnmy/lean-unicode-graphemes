import Segmentation

-- "H1, partition: the clusters put back together are the input, and none is empty."
theorem «H1b rejects a segmenter that returns an empty cluster» :
    ¬ Segmentation.H1b (fun _ => [""]) := by
  intro h
  exact h "" "" (by simp) rfl
