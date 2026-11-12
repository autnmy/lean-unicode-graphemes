import Segmentation

-- "Prove that the clusters put back together are the input, and that no cluster is empty."
-- A text that starts with a combining mark, then a lone CR, then CR LF exercises the break rules
-- most likely to drop or duplicate a code point; the theorem must cover it for every string.
theorem «graphemes_join covers a lone CR before CRLF and a combining mark» :
    String.join (Segmentation.graphemes "\u0301\r\r\na\u200D") = "\u0301\r\r\na\u200D" :=
  Segmentation.graphemes_join "\u0301\r\r\na\u200D"
