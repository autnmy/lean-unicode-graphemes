import TableGen.Ucd

/-!
# Writing the property tables as Lean modules

`renderAll` turns the text of the UCD files into the three generated table
modules under `Segmentation/Tables/`. Each module starts with the Unicode
licence text, copied verbatim into a Lean comment, because the Unicode License
v3 covers every table generated from the data.

A Lean list literal with thousands of elements is slow to elaborate, so each
table is written as several literals of at most `chunkSize` ranges, joined into
one array. The output depends only on the file text: no dates, no paths from
the machine, and the ranges in the sorted order `normalize` returns. Running
the generator twice therefore writes the same bytes, which the drift check in
CI relies on.
-/

namespace TableGen

open Segmentation Segmentation.Tables

/-- The most ranges one list literal in a generated module holds. -/
def chunkSize : Nat := 256

/-- `true` when `chars` holds `a` followed directly by `b`. -/
def containsPair (a b : Char) : List Char → Bool
  | [] => false
  | c :: rest =>
    match rest with
    | d :: _ => (c == a && d == b) || containsPair a b rest
    | [] => false

/--
The licence wrapped in a Lean block comment. Lean block comments nest, so a
`/-` or `-/` inside the text would change where the comment ends and turn part
of the licence into code; such a text is refused.
-/
def licenceHeader (licence : String) : Except String String :=
  let chars := licence.toList
  if containsPair '-' '/' chars || containsPair '/' '-' chars then
    .error "LICENSE.txt contains `/-` or `-/`, which would break the generated comment header"
  else
    let body := if licence.endsWith "\n" then licence else licence ++ "\n"
    .ok s!"/-\n{body}-/\n"

/-- `n` in upper-case hexadecimal, at least four digits, as the UCD files write code points. -/
def hex (n : Nat) : String :=
  let digits := (Nat.toDigits 16 n).map Char.toUpper
  "0x" ++ String.ofList (List.replicate (4 - digits.length) '0' ++ digits)

/-- `list` cut into pieces of at most `size` elements, in order. -/
def chunks {α : Type} (size : Nat) (list : List α) : List (List α) :=
  -- Each piece takes at least one element, so `list.length` steps are enough.
  go list.length list
where
  go : Nat → List α → List (List α)
    | _, [] => []
    | 0, rest => [rest]
    | steps + 1, rest => rest.take (max size 1) :: go steps (rest.drop (max size 1))

/-- How one table is written: its module, its array's name, and its value's type. -/
structure TableSpec (α : Type) where
  /-- The module file, relative to the package root. -/
  path : System.FilePath
  /-- The UCD file the table comes from, relative to `dataDir`. -/
  source : String
  /-- What the module's doc comment says the table holds. -/
  description : String
  /-- The name of the generated array, inside `Segmentation.Tables`. -/
  arrayName : String
  /-- The value type, as Lean code. -/
  valueType : String
  /-- One value, as Lean code that elaborates against `valueType`. -/
  valueCode : α → String

def gcbCode : GCB → String
  | .CR => ".CR" | .LF => ".LF" | .Control => ".Control" | .Extend => ".Extend"
  | .ZWJ => ".ZWJ" | .RI => ".RI" | .Prepend => ".Prepend"
  | .SpacingMark => ".SpacingMark" | .L => ".L" | .V => ".V" | .T => ".T"
  | .LV => ".LV" | .LVT => ".LVT" | .Other => ".Other"

def incbCode : InCB → String
  | .Consonant => ".Consonant" | .Extend => ".Extend" | .Linker => ".Linker"
  | .None => ".None"

def gcbSpec : TableSpec GCB where
  path := "Segmentation" / "Tables" / "GraphemeClusterBreak.lean"
  source := "auxiliary/GraphemeBreakProperty.txt"
  description := "`Grapheme_Cluster_Break` ranges. Code points no range holds are `Other`."
  arrayName := "gcbRanges"
  valueType := "GCB"
  valueCode := gcbCode

def extPictSpec : TableSpec Bool where
  path := "Segmentation" / "Tables" / "ExtendedPictographic.lean"
  source := "emoji/emoji-data.txt"
  description := "`Extended_Pictographic` ranges, all `true`. Code points no range holds are `false`."
  arrayName := "extPictRanges"
  valueType := "Bool"
  valueCode := fun b => toString b

def incbSpec : TableSpec InCB where
  path := "Segmentation" / "Tables" / "IndicConjunctBreak.lean"
  source := "DerivedCoreProperties.txt"
  description := "`Indic_Conjunct_Break` ranges. Code points no range holds are `None`."
  arrayName := "incbRanges"
  valueType := "InCB"
  valueCode := incbCode

/-- The text of one generated module holding `ranges`. -/
def renderModule {α : Type} (header : String) (spec : TableSpec α) (ranges : List (Range α)) :
    String :=
  let pieces := chunks chunkSize ranges
  let chunkName (i : Nat) := s!"{spec.arrayName}Chunk{i}"
  let renderRange (r : Range α) := s!"  ⟨{hex r.lo}, {hex r.hi}, {spec.valueCode r.value}⟩"
  let renderChunk (i : Nat) (piece : List (Range α)) :=
    s!"private def {chunkName i} : List (Range {spec.valueType}) := [\n" ++
    ",\n".intercalate (piece.map renderRange) ++ "\n]\n\n"
  let chunkDefs := String.join ((List.range pieces.length).zip pieces |>.map
    fun (i, piece) => renderChunk i piece)
  let joined := " ++ ".intercalate ((List.range pieces.length).map chunkName)
  let joined := if pieces.isEmpty then "[]" else joined
  header ++
  s!"-- Generated by `lake exe gen-tables` from data/ucd/{unicodeVersion}/{spec.source}.\n" ++
  "-- Do not edit by hand: CI regenerates this file and fails on any difference.\n\n" ++
  "import Segmentation.Statements\nimport Segmentation.Tables.Range\n\n" ++
  "namespace Segmentation.Tables\n\n" ++
  chunkDefs ++
  s!"/-- {spec.description} Sorted by `lo`, with no overlapping ranges. -/\n" ++
  s!"def {spec.arrayName} : Array (Range {spec.valueType}) :=\n  ({joined}).toArray\n\n" ++
  "end Segmentation.Tables\n"

/--
The three generated table modules, as (path, contents), from the text of
`LICENSE.txt` and the three UCD files. Fails if the licence cannot be put in a
comment, or if a file does not parse.
-/
def renderAll (licence gcbText extPictText incbText : String) :
    Except String (List (System.FilePath × String)) := do
  -- The licence is checked first, so a broken header fails before any parsing.
  let header ← licenceHeader licence
  let gcb ← normalize (← parseGcb gcbText)
  let extPict ← normalize (← parseExtPict extPictText)
  let incb ← normalize (← parseIncb incbText)
  pure [
    (gcbSpec.path, renderModule header gcbSpec gcb),
    (extPictSpec.path, renderModule header extPictSpec extPict),
    (incbSpec.path, renderModule header incbSpec incb)
  ]

end TableGen
