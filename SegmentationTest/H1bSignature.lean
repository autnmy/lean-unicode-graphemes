import Segmentation

-- "The statements take the property lookup and the segmenter as parameters, so this file needs neither to exist yet."
theorem «H1b is stated over the segmenter alone» : True :=
  let _h1b : (String → List String) → Prop := Segmentation.H1b
  trivial
