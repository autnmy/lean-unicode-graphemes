import Segmentation

-- "Prove that the clusters put back together are the input, and that no cluster is empty."
-- The empty text and a text that ends with a lone CR are where an empty trailing cluster would appear.
theorem «graphemes_ne_empty rules out an empty cluster for the empty string and a lone CR» :
    (∀ g ∈ Segmentation.graphemes "", g ≠ "") ∧ (∀ g ∈ Segmentation.graphemes "a\r", g ≠ "") :=
  ⟨Segmentation.graphemes_ne_empty "", Segmentation.graphemes_ne_empty "a\r"⟩
