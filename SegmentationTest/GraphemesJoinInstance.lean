import Segmentation

-- H1a must hold for every string, including the empty one and text that splits into several
-- clusters (a base letter with a combining mark, then CR LF, then a letter).
theorem «graphemes_join gives back a multi-cluster string with combining mark and CRLF» :
    String.join (Segmentation.graphemes "") = "" ∧
      String.join (Segmentation.graphemes "e\u0301\r\nx") = "e\u0301\r\nx" :=
  ⟨Segmentation.graphemes_join "", Segmentation.graphemes_join "e\u0301\r\nx"⟩
