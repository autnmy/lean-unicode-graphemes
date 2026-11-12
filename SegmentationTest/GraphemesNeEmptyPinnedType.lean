import Segmentation

-- "`theorem graphemes_join : Segmentation.H1a Segmentation.graphemes` and `theorem graphemes_ne_empty : Segmentation.H1b Segmentation.graphemes`, against the statements committed in L3."
-- The ascription fails if the theorem is missing, renamed, or stated about another segmenter or statement.
theorem «graphemes_ne_empty proves H1b for the real segmenter, not a weaker statement» :
    Segmentation.H1b Segmentation.graphemes :=
  Segmentation.graphemes_ne_empty
