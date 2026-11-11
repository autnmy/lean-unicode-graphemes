import Segmentation

-- The final theorem is written `theorem graphemes_join : H1a graphemes`, so H1a takes the segmenter alone.
theorem «H1a takes only the segmenter» :
    (Segmentation.H1a : (String → List String) → Prop) = Segmentation.H1a := rfl
