import Segmentation

-- Later proofs apply H2' as `H2' graphemes boundaries`. A swapped variable order, or an
-- unused `props` parameter, would make this ascription fail.
theorem «H2' takes the segmenter first and the boundary function second» : True := by
  have _h2' : (String → List String) → (String → List Nat) → Prop := Segmentation.H2'
  trivial
