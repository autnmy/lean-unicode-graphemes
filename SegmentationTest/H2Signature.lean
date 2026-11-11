import Segmentation

-- "The statements take the property lookup and the segmenter as parameters, so this file needs neither to exist yet."
-- Later proofs apply `H2 props graphemes`, so the parameter order is part of the statement.
theorem «H2 takes the property lookup and then the segmenter» : True :=
  let _h2 : (Char → Segmentation.Props) → (String → List String) → Prop := Segmentation.H2
  trivial
