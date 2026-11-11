import Segmentation

-- Later proofs apply H2 as `H2 props graphemes`. If the section variables were declared
-- in another order, or H2 picked up `boundaries`, this ascription would not type-check.
theorem «H2 takes the property lookup first and the segmenter second» : True := by
  have _h2 : (Char → Segmentation.Props) → (String → List String) → Prop := Segmentation.H2
  trivial
