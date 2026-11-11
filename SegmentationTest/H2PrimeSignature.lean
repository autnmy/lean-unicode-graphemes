import Segmentation

-- "The statements take the property lookup and the segmenter as parameters, so this file needs neither to exist yet."
-- Later proofs apply `H2' graphemes boundaries`, so the parameter order is part of the statement.
theorem «H2' takes graphemes and then boundaries» : True :=
  let _h2' : (String → List String) → (String → List Nat) → Prop := Segmentation.H2'
  trivial
