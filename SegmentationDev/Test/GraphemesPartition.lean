import Segmentation

/-!
Checks of the partition theorems in `Segmentation.Partition`: the clusters of `graphemes` join
back to the input (`JoinRestoresInput`), and no cluster is empty (`ClustersNonEmpty`).
-/

-- The type ascriptions pin each theorem to the committed statement applied to the real
-- segmenter, so a theorem that is missing, renamed, or about a weaker statement or a different
-- segmenter fails here.
theorem «graphemes_join is stated as JoinRestoresInput applied to graphemes» :
    Segmentation.JoinRestoresInput Segmentation.graphemes :=
  Segmentation.graphemes_join

theorem «graphemes_ne_empty is stated as ClustersNonEmpty applied to graphemes» :
    Segmentation.ClustersNonEmpty Segmentation.graphemes :=
  Segmentation.graphemes_ne_empty

-- JoinRestoresInput must hold for every string, including the empty one and text that splits
-- into several clusters (a base letter with a combining mark, then CR LF, then a letter).
theorem «graphemes_join gives back a multi-cluster string with combining mark and CRLF» :
    String.join (Segmentation.graphemes "") = "" ∧
      String.join (Segmentation.graphemes "e\u0301\r\nx") = "e\u0301\r\nx" :=
  ⟨Segmentation.graphemes_join "", Segmentation.graphemes_join "e\u0301\r\nx"⟩

-- A text that starts with a combining mark, then a lone CR, then CR LF exercises the break rules
-- most likely to drop or duplicate a code point.
theorem «graphemes_join covers a lone CR before CRLF and a combining mark» :
    String.join (Segmentation.graphemes "\u0301\r\r\na\u200D") = "\u0301\r\r\na\u200D" :=
  Segmentation.graphemes_join "\u0301\r\r\na\u200D"

-- The empty string never appears among the clusters of a text made of several clusters.
theorem «graphemes_ne_empty rules out an empty first cluster» :
    "" ∉ Segmentation.graphemes "e\u0301\r\nx" :=
  fun h => Segmentation.graphemes_ne_empty "e\u0301\r\nx" "" h rfl

-- The empty text and a text that ends with a lone CR are where an empty trailing cluster would
-- appear.
theorem «graphemes_ne_empty rules out an empty cluster for the empty string and a lone CR» :
    (∀ g ∈ Segmentation.graphemes "", g ≠ "") ∧ (∀ g ∈ Segmentation.graphemes "a\r", g ≠ "") :=
  ⟨Segmentation.graphemes_ne_empty "", Segmentation.graphemes_ne_empty "a\r"⟩

-- The axiom check for `graphemes_join` and `graphemes_ne_empty` is in
-- `SegmentationDev.Test.HeadlineAxioms`, with the other headline theorems.
