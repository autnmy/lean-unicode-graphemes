import Segmentation
import TableGen

/-!
# UCD parser checks

Compile-time checks of the parsers, `normalize`, `paint` and `checkDigestList`
in `TableGen.Ucd`. The expected constructors are written out here rather than
read from `TableGen.gcbNames` or `TableGen.incbNames`: the generator and the
exhaustive table check share those maps, so a wrong entry there would agree
with itself everywhere else. The test driver imports this module, so a failed
`#guard` stops `lake test`.
-/

namespace SegmentationTest.UcdChecks

open Segmentation Segmentation.Tables

/-- The single entry `text` parses to, as `(lo, hi, value)`, or `none` on an error or another count. -/
def single {α : Type} : Except String (List (Range α)) → Option (Nat × Nat × α)
  | .ok [r] => some (r.lo, r.hi, r.value)
  | _ => none

def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

-- Every Grapheme_Cluster_Break name the file uses, against the constructor it must give.
#guard single (TableGen.parseGcb "0041 ; CR # x") == some (0x41, 0x41, GCB.CR)
#guard single (TableGen.parseGcb "0041 ; LF # x") == some (0x41, 0x41, GCB.LF)
#guard single (TableGen.parseGcb "0041 ; Control # x") == some (0x41, 0x41, GCB.Control)
#guard single (TableGen.parseGcb "0041 ; Extend # x") == some (0x41, 0x41, GCB.Extend)
#guard single (TableGen.parseGcb "0041 ; ZWJ # x") == some (0x41, 0x41, GCB.ZWJ)
#guard single (TableGen.parseGcb "0041 ; Regional_Indicator # x") == some (0x41, 0x41, GCB.RI)
#guard single (TableGen.parseGcb "0041 ; Prepend # x") == some (0x41, 0x41, GCB.Prepend)
#guard single (TableGen.parseGcb "0041 ; SpacingMark # x") == some (0x41, 0x41, GCB.SpacingMark)
#guard single (TableGen.parseGcb "0041 ; L # x") == some (0x41, 0x41, GCB.L)
#guard single (TableGen.parseGcb "0041 ; V # x") == some (0x41, 0x41, GCB.V)
#guard single (TableGen.parseGcb "0041 ; T # x") == some (0x41, 0x41, GCB.T)
#guard single (TableGen.parseGcb "0041 ; LV # x") == some (0x41, 0x41, GCB.LV)
#guard single (TableGen.parseGcb "0041 ; LVT # x") == some (0x41, 0x41, GCB.LVT)

-- A range, as the file writes it, with comment lines around it.
#guard single (TableGen.parseGcb "# @missing: 0000..10FFFF; Other\n\n0300..036F    ; Extend # Mn [112] x\n") ==
  some (0x300, 0x36F, GCB.Extend)

-- Every InCB value a line can carry. A text with only other properties' lines
-- parses to nothing, which is an error; ParseIncbOtherProperties.lean checks
-- that such lines are skipped beside an InCB line.
#guard single (TableGen.parseIncb "0041 ; InCB; Consonant # x") == some (0x41, 0x41, InCB.Consonant)
#guard single (TableGen.parseIncb "0041 ; InCB; Extend # x") == some (0x41, 0x41, InCB.Extend)
#guard single (TableGen.parseIncb "0041 ; InCB; Linker # x") == some (0x41, 0x41, InCB.Linker)
#guard isError (TableGen.parseIncb "0041 ; Alphabetic # x")
#guard isError (TableGen.parseIncb "094D ; InCB # value missing")

-- emoji-data.txt writes no space before the comment.
#guard single (TableGen.parseExtPict "00A9          ; Extended_Pictographic# E0.6   [1] (©️)       copyright") ==
  some (0xA9, 0xA9, true)

-- Malformed input is an error, never a default. ParseGcbUnknownName.lean checks
-- a misspelled value name.
#guard isError (TableGen.parseGcb "110000 ; Control # x")
#guard isError (TableGen.parseGcb "0045..0041 ; Control # x")
#guard isError (TableGen.parseGcb "zz ; ;")
#guard isError (TableGen.parseGcb "")
#guard isError (TableGen.parseGcb "# only a comment\n")

-- An unknown value beside a valid row still fails the whole parse, so the
-- rejection does not depend on the parse ending up empty.
#guard isError (TableGen.parseGcb "0041 ; Control # x\n1F1E6 ; Regional_Indicatr # x\n")
#guard isError (TableGen.parseIncb "0915 ; InCB; Consonant # x\n094D ; InCB; Linkr # x\n")

-- Overlapping entries with different values. NormalizeConflictingOverlap.lean
-- checks that `normalize` rejects the same entries.
def overlapping : List (Range GCB) :=
  [{ lo := 0x41, hi := 0x45, value := .Control }, { lo := 0x43, hi := 0x43, value := .Extend }]

#guard isError (TableGen.paint GCB.Other overlapping)

-- `normalize` sorts and joins touching ranges of one value, and keeps others apart.
def mergeResult : Option (List (Nat × Nat × GCB)) :=
  match TableGen.normalize
      [({ lo := 0x50, hi := 0x50, value := .Extend } : Range GCB),
       { lo := 0x43, hi := 0x43, value := .L }, { lo := 0x41, hi := 0x42, value := .L }] with
  | .ok ranges => some (ranges.map fun r => (r.lo, r.hi, r.value))
  | .error _ => none

#guard mergeResult == some [(0x41, 0x43, GCB.L), (0x50, 0x50, GCB.Extend)]

-- `paint` gives every code point a value, the default where no entry lists it.
def painted : Option (Array GCB) :=
  match TableGen.paint GCB.Other [{ lo := 0x41, hi := 0x42, value := .L }] with
  | .ok values => some values
  | .error _ => none

#guard (painted.map (·.size)) == some 0x110000
#guard (painted.bind (·[0x41]?)) == some GCB.L
#guard (painted.bind (·[0x42]?)) == some GCB.L
#guard (painted.bind (·[0x43]?)) == some GCB.Other
#guard (painted.bind (·[0x10FFFF]?)) == some GCB.Other

-- The digest list must name exactly the five expected files.
def digestLine (path : String) : String :=
  "0839dcb79e4ac639ecd538b1abf7c9d22e3f9dd265b7e182d33627aa4d75b45a  " ++ path ++ "\n"

def fiveLines : String := String.join (TableGen.digestFiles.map digestLine)

#guard !isError (TableGen.checkDigestList fiveLines)
#guard isError (TableGen.checkDigestList (String.join ((TableGen.digestFiles.take 4).map digestLine)))
#guard isError (TableGen.checkDigestList (fiveLines ++ digestLine "README.md"))
#guard isError (TableGen.checkDigestList (fiveLines ++ digestLine "LICENSE.txt"))
#guard isError (TableGen.checkDigestList
  (String.join ((TableGen.digestFiles.take 4).map digestLine) ++ digestLine "../README.md"))
#guard isError (TableGen.checkDigestList
  (String.join ((TableGen.digestFiles.take 4).map digestLine) ++ "0839  LICENSE.txt\n"))

end SegmentationTest.UcdChecks
