import Segmentation

-- "H2', the two functions agree." `cutPoints []` is `[0]`, so a segmenter that returns no
-- clusters agrees with a boundary function that returns `[0]`. Passing them in the other
-- order does not type-check, which pins `H2' graphemes boundaries`.
theorem «H2' holds when boundaries is the cut points of graphemes on empty output» :
    Segmentation.H2' (fun _ => ([] : List String)) (fun _ => [0]) := by
  intro _
  rfl
