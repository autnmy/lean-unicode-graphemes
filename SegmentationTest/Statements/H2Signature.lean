import Segmentation

-- The final theorem is applied as `H2 props graphemes`, so the parameter order is part of the statement.
theorem «H2 takes the property lookup then the segmenter» :
    (Segmentation.H2 : (Char → Segmentation.Props) → (String → List String) → Prop) =
      Segmentation.H2 := rfl
