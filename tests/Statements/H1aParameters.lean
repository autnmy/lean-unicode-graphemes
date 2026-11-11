import Segmentation

-- "The statements take the property lookup and the segmenter as parameters, so this file needs neither to exist yet."
-- H1a mentions only `graphemes`, so it must not also demand the property lookup or the
-- boundary function; a stray parameter would make this ascription fail.
theorem «H1a depends on the segmenter alone» : True := by
  have _h1a : (String → List String) → Prop := Segmentation.H1a
  trivial
