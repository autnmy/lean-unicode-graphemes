import Segmentation

/-!
# Reading a GraphemeBreakTest.txt line

The rule checks write each line of `data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt` as the
code point numbers the file prints. Lean's `\u` string escape takes exactly four hex digits, so
code points above U+FFFF (regional indicators, emoji) cannot be written in a string literal.
These helpers build the text from the numbers and give the clusters back as numbers, so the
expected values stay hand-copied lists that do not pass through the segmenter.
-/

namespace SegmentationDev.Test.GraphemeBreakTestLine

/-- The text made of the code points `cps`. -/
def text (cps : List Nat) : String := String.ofList (cps.map Char.ofNat)

/-- The clusters `Segmentation.graphemes` gives for the code points `cps`, each as its code
point numbers. -/
def clusters (cps : List Nat) : List (List Nat) :=
  (Segmentation.graphemes (text cps)).map fun g => g.toList.map Char.toNat

/-- The positions `Segmentation.boundaries` gives for the code points `cps`. -/
def cuts (cps : List Nat) : List Nat := Segmentation.boundaries (text cps)

end SegmentationDev.Test.GraphemeBreakTestLine
