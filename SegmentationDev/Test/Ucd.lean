import Segmentation
import SegmentationDev.TableGen

/-!
# UCD parser checks

Compile-time checks of the parsers, `normalize`, `paint` and `checkDigestList`
in `SegmentationDev.TableGen.Ucd`. The expected constructors are written out here rather than
read from `SegmentationDev.TableGen.gcbNames` or `SegmentationDev.TableGen.incbNames`: the
generator and the exhaustive table check share those maps, so a wrong entry there would agree
with itself everywhere else. The test driver imports this module, so a failed
`#guard` stops `lake test`.
-/

namespace SegmentationDev.Test.UcdChecks

open Segmentation Segmentation.Tables

/-- The single entry `text` parses to, as `(lo, hi, value)`, or `none` on an error or another count. -/
def single {α : Type} : Except String (List (Range α)) → Option (Nat × Nat × α)
  | .ok [r] => some (r.lo, r.hi, r.value)
  | _ => none

def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

-- Every Grapheme_Cluster_Break name the file uses, against the constructor it must give.
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; CR # x") == some (0x41, 0x41, GCB.cr)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; LF # x") == some (0x41, 0x41, GCB.lf)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; Control # x") == some (0x41, 0x41, GCB.control)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; Extend # x") == some (0x41, 0x41, GCB.extend)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; ZWJ # x") == some (0x41, 0x41, GCB.zwj)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; Regional_Indicator # x") == some (0x41, 0x41, GCB.regionalIndicator)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; Prepend # x") == some (0x41, 0x41, GCB.prepend)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; SpacingMark # x") == some (0x41, 0x41, GCB.spacingMark)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; L # x") == some (0x41, 0x41, GCB.l)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; V # x") == some (0x41, 0x41, GCB.v)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; T # x") == some (0x41, 0x41, GCB.t)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; LV # x") == some (0x41, 0x41, GCB.lv)
#guard single (SegmentationDev.TableGen.parseGcb "0041 ; LVT # x") == some (0x41, 0x41, GCB.lvt)

-- A range, as the file writes it, with comment lines around it.
#guard single (SegmentationDev.TableGen.parseGcb "# @missing: 0000..10FFFF; Other\n\n0300..036F    ; Extend # Mn [112] x\n") ==
  some (0x300, 0x36F, GCB.extend)

-- Every InCB value a line can carry. A text with only other properties' lines
-- parses to nothing, which is an error.
#guard single (SegmentationDev.TableGen.parseIncb "0041 ; InCB; Consonant # x") == some (0x41, 0x41, InCB.consonant)
#guard single (SegmentationDev.TableGen.parseIncb "0041 ; InCB; Extend # x") == some (0x41, 0x41, InCB.extend)
#guard single (SegmentationDev.TableGen.parseIncb "0041 ; InCB; Linker # x") == some (0x41, 0x41, InCB.linker)
#guard isError (SegmentationDev.TableGen.parseIncb "0041 ; Alphabetic # x")
#guard isError (SegmentationDev.TableGen.parseIncb "094D ; InCB # value missing")

-- DerivedCoreProperties.txt mixes many properties. A parser that read the wrong field would take
-- another property's lines as InCB, or lose the three-field InCB line.
-- `decide` decodes the string literal while elaborating, one nested step per
-- character, which needs more than the default recursion depth.
set_option maxRecDepth 20000 in
theorem parseIncb_reads_incb_lines_value_from_third_field :
    (match SegmentationDev.TableGen.parseIncb
        "0915          ; Alphabetic # Lo       DEVANAGARI LETTER KA\n094D          ; InCB; Linker # Mn       DEVANAGARI SIGN VIRAMA\n" with
     | .ok [r] => r.lo == 0x094D && r.hi == 0x094D && r.value == Segmentation.InCB.linker
     | _ => false) = true := by decide

-- Only Consonant, Extend and Linker are InCB values the type can hold.
-- Any other value on an InCB line must stop the parse.
theorem parseIncb_rejects_unknown_value :
    (SegmentationDev.TableGen.parseIncb "094D ; InCB; Linkr # misspelled\n" matches .error _) = true := by
  decide

-- emoji-data.txt writes no space before the comment.
#guard single (SegmentationDev.TableGen.parseExtPict "00A9          ; Extended_Pictographic# E0.6   [1] (©️)       copyright") ==
  some (0xA9, 0xA9, true)

-- An empty or truncated file would make every code point read `false` on both the generator and
-- the reference side, so an empty parse result must be an error.
theorem parseExtPict_fails_without_entries :
    (match SegmentationDev.TableGen.parseExtPict "# emoji-data.txt\n\n0023          ; Emoji                # E0.0   [1] (#\uFE0F)       hash sign\n" with
     | .error _ => true
     | .ok _ => false) = true := by decide

-- Malformed input is an error, never a default.
#guard isError (SegmentationDev.TableGen.parseGcb "110000 ; Control # x")
#guard isError (SegmentationDev.TableGen.parseGcb "0045..0041 ; Control # x")
#guard isError (SegmentationDev.TableGen.parseGcb "zz ; ;")
#guard isError (SegmentationDev.TableGen.parseGcb "")
#guard isError (SegmentationDev.TableGen.parseGcb "# only a comment\n")

-- The generator and the reference share this parser, so a name it does not know must be an
-- error: read as the default `Other`, both sides would agree and the exhaustive check would pass.
theorem parseGcb_rejects_misspelled_value :
    (match SegmentationDev.TableGen.parseGcb "1F1E6..1F1FF  ; Regional_Indicatr # So  [26] REGIONAL INDICATOR SYMBOL LETTER A..Z\n" with
     | .error _ => true
     | .ok _ => false) = true := by decide

-- An unknown value beside a valid row still fails the whole parse, so the
-- rejection does not depend on the parse ending up empty.
#guard isError (SegmentationDev.TableGen.parseGcb "0041 ; Control # x\n1F1E6 ; Regional_Indicatr # x\n")
#guard isError (SegmentationDev.TableGen.parseIncb "0915 ; InCB; Consonant # x\n094D ; InCB; Linkr # x\n")

-- Overlapping entries with different values: U+0043 is claimed by both. Keeping
-- either one silently would write a table that no longer says what the file says.
def overlapping : List (Range GCB) :=
  [{ lo := 0x41, hi := 0x45, value := .control }, { lo := 0x43, hi := 0x43, value := .extend }]

#guard isError (SegmentationDev.TableGen.paint GCB.other overlapping)

theorem normalize_rejects_overlapping_entries_with_different_values :
    (match SegmentationDev.TableGen.normalize
        [({ lo := 0x41, hi := 0x45, value := Segmentation.GCB.control } : Segmentation.Tables.Range Segmentation.GCB),
         { lo := 0x43, hi := 0x43, value := Segmentation.GCB.extend }] with
     | .error _ => true
     | .ok _ => false) = true := by decide

-- `normalize` sorts and joins touching ranges of one value, and keeps others apart.
def mergeResult : Option (List (Nat × Nat × GCB)) :=
  match SegmentationDev.TableGen.normalize
      [({ lo := 0x50, hi := 0x50, value := .extend } : Range GCB),
       { lo := 0x43, hi := 0x43, value := .l }, { lo := 0x41, hi := 0x42, value := .l }] with
  | .ok ranges => some (ranges.map fun r => (r.lo, r.hi, r.value))
  | .error _ => none

#guard mergeResult == some [(0x41, 0x43, GCB.l), (0x50, 0x50, GCB.extend)]

-- `paint` gives every code point a value, the default where no entry lists it.
def painted : Option (Array GCB) :=
  match SegmentationDev.TableGen.paint GCB.other [{ lo := 0x41, hi := 0x42, value := .l }] with
  | .ok values => some values
  | .error _ => none

#guard (painted.map (·.size)) == some 0x110000
#guard (painted.bind (·[0x41]?)) == some GCB.l
#guard (painted.bind (·[0x42]?)) == some GCB.l
#guard (painted.bind (·[0x43]?)) == some GCB.other
#guard (painted.bind (·[0x10FFFF]?)) == some GCB.other

-- The digest list must name exactly the five expected files.
def digestLine (path : String) : String :=
  "0839dcb79e4ac639ecd538b1abf7c9d22e3f9dd265b7e182d33627aa4d75b45a  " ++ path ++ "\n"

def fiveLines : String := String.join (SegmentationDev.TableGen.digestFiles.map digestLine)

#guard !isError (SegmentationDev.TableGen.checkDigestList fiveLines)
#guard isError (SegmentationDev.TableGen.checkDigestList (String.join ((SegmentationDev.TableGen.digestFiles.take 4).map digestLine)))
#guard isError (SegmentationDev.TableGen.checkDigestList (fiveLines ++ digestLine "README.md"))
#guard isError (SegmentationDev.TableGen.checkDigestList (fiveLines ++ digestLine "LICENSE.txt"))
#guard isError (SegmentationDev.TableGen.checkDigestList
  (String.join ((SegmentationDev.TableGen.digestFiles.take 4).map digestLine) ++ digestLine "../README.md"))
#guard isError (SegmentationDev.TableGen.checkDigestList
  (String.join ((SegmentationDev.TableGen.digestFiles.take 4).map digestLine) ++ "0839  LICENSE.txt\n"))

end SegmentationDev.Test.UcdChecks
