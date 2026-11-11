import Segmentation

-- "The statements take the property lookup and the segmenter as parameters, so this file needs neither to exist yet."
theorem «H1a is stated over the segmenter alone» : True :=
  let _h1a : (String → List String) → Prop := Segmentation.H1a
  trivial
