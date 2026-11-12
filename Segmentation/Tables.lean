import Segmentation.Statements
import Segmentation.Tables.Range
import Segmentation.Tables.GraphemeClusterBreak
import Segmentation.Tables.ExtendedPictographic
import Segmentation.Tables.IndicConjunctBreak

/-!
# Property lookup

The three properties the grapheme cluster rules read, looked up in the tables
`lake exe gen-tables` generates from the Unicode 18.0.0 data files.

The lookups by number cover every code point U+0000..U+10FFFF, including the
surrogates U+D800..U+DFFF, which a `Char` cannot hold. `props` reads a `Char`
through them, so the two always agree.
-/

namespace Segmentation.Tables

/-- The `Grapheme_Cluster_Break` value of code point `n`. -/
def gcbOf (n : Nat) : GCB := Range.lookup .Other gcbRanges n

/-- Whether code point `n` is `Extended_Pictographic`. -/
def extPictOf (n : Nat) : Bool := Range.lookup false extPictRanges n

/-- The `Indic_Conjunct_Break` value of code point `n`. -/
def incbOf (n : Nat) : InCB := Range.lookup .None incbRanges n

/-- The three properties of `c` the grapheme cluster rules read. -/
def props (c : Char) : Props :=
  { gcb := gcbOf c.toNat, extPict := extPictOf c.toNat, incb := incbOf c.toNat }

end Segmentation.Tables
