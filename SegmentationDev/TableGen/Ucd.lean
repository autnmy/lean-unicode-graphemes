import Segmentation.Statements
import Segmentation.Version
import Segmentation.Tables.Range

/-!
# Reading the Unicode Character Database files

Parsers for the three properties the grapheme cluster rules read, as the UCD
files state them, and the checks around them:

* `parseGcb` reads `auxiliary/GraphemeBreakProperty.txt`.
* `parseExtPict` reads `emoji/emoji-data.txt`, keeping only `Extended_Pictographic`.
* `parseIncb` reads `DerivedCoreProperties.txt`, keeping only `InCB` lines.

The generator and the exhaustive table check both read the files through these
parsers, so the parsers are strict: a line they cannot read, a value name they
do not know, or a code point past U+10FFFF is an error, never a default value.
A default would give the same wrong answer on both sides, and the check would
not see it.

Each parser returns the file's entries in file order. `normalize` turns them
into the sorted, merged range list the generator writes; `paint` turns them into
one value per code point, which is the reference the table check compares with.
The two are kept apart so a bug in one shows up as a mismatch with the other.

The text handling works on `List Char` with structural recursion only, so
`decide` can evaluate the parsers on small inputs in the kernel.
-/

namespace SegmentationDev.TableGen

open Segmentation Segmentation.Tables

/-- The last Unicode code point. -/
def maxCodePoint : Nat := 0x10FFFF

/-- The directory holding the UCD files for the Unicode version the library implements. -/
def dataDir : System.FilePath := "data" / "ucd" / Segmentation.unicodeVersion

/--
The files `SHA256SUMS` must list, relative to `dataDir`: every file the
generator and the table checks read, and the grapheme break test file.
-/
def digestFiles : List String := [
  "auxiliary/GraphemeBreakProperty.txt",
  "auxiliary/GraphemeBreakTest.txt",
  "emoji/emoji-data.txt",
  "DerivedCoreProperties.txt",
  "LICENSE.txt"
]

/-- The UCD spelling of each `Grapheme_Cluster_Break` value the rules use. -/
def gcbNames : List (String × GCB) := [
  ("CR", .cr), ("LF", .lf), ("Control", .control), ("Extend", .extend),
  ("ZWJ", .zwj), ("Regional_Indicator", .regionalIndicator), ("Prepend", .prepend),
  ("SpacingMark", .spacingMark), ("L", .l), ("V", .v), ("T", .t),
  ("LV", .lv), ("LVT", .lvt)
]

/--
The UCD spelling of each `Indic_Conjunct_Break` value a file line can carry.
`.none` is the value of every code point no line lists.
-/
def incbNames : List (String × InCB) := [
  ("Consonant", .consonant), ("Extend", .extend), ("Linker", .linker)
]

/-! ## Text helpers on `List Char` -/

/-- Splits `chars` at every `sep`, keeping empty pieces. -/
def splitOnChar (sep : Char) (chars : List Char) : List (List Char) :=
  go chars []
where
  /-- `current` holds the characters of the piece being read, reversed. -/
  go : List Char → List Char → List (List Char)
    | [], current => [current.reverse]
    | c :: rest, current =>
      if c == sep then current.reverse :: go rest [] else go rest (c :: current)

/-- `chars` up to the first `#`: a UCD line without its comment. -/
def dropComment : List Char → List Char
  | [] => []
  | c :: rest => if c == '#' then [] else c :: dropComment rest

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-- `chars` without leading and trailing spaces and tabs. -/
def trim (chars : List Char) : List Char :=
  ((chars.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- The value of one hexadecimal digit, upper or lower case. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A non-empty string of hexadecimal digits, read as a number. -/
def parseHex? (chars : List Char) : Option Nat :=
  if chars.isEmpty then none else go chars 0
where
  go : List Char → Nat → Option Nat
    | [], acc => some acc
    | c :: rest, acc =>
      match hexDigit? c with
      | some digit => go rest (acc * 16 + digit)
      | none => none

/-- The value `name` stands for in `names`, compared character by character. -/
def lookupName {α : Type} (names : List (String × α)) (name : List Char) : Option α :=
  match names with
  | [] => none
  | (spelling, value) :: rest =>
    if spelling.toList == name then some value else lookupName rest name

/-! ## Lines -/

/--
The code points a UCD line's first field names: `XXXX` or `XXXX..YYYY`, within
U+0000..U+10FFFF and with the first not after the last.
-/
def parseCodePoints (field : List Char) : Except String (Nat × Nat) :=
  let bounds : Option (Nat × Nat) :=
    match splitOnChar '.' field with
    | [one] => (fun n => (n, n)) <$> parseHex? one
    | [lo, [], hi] => do
      let lo ← parseHex? lo
      let hi ← parseHex? hi
      pure (lo, hi)
    | _ => none
  match bounds with
  | none => .error s!"not a code point or code point range: {String.ofList field}"
  | some (lo, hi) =>
    if hi > maxCodePoint then
      .error s!"code point past U+10FFFF: {String.ofList field}"
    else if lo > hi then
      .error s!"range ends before it starts: {String.ofList field}"
    else
      .ok (lo, hi)

/--
The `;`-separated fields of every line of `text` that holds data, trimmed, with
comments and blank lines dropped.
-/
def dataLines (text : String) : List (List (List Char)) :=
  (splitOnChar '\n' text.toList).filterMap fun line =>
    let content := trim (dropComment line)
    if content.isEmpty then none else some ((splitOnChar ';' content).map trim)

/--
Reads every data line of `text` with `entry`, which returns `none` for a line
of another property and an error for a line it cannot read. Fails when the file
yields no entry at all, so an empty or truncated file is an error rather than
a table of defaults.
-/
def parseEntries {α : Type} (property : String) (text : String)
    (entry : List (List Char) → Except String (Option (Range α))) :
    Except String (List (Range α)) := do
  let entries ← go (dataLines text)
  if entries.isEmpty then
    .error s!"no {property} entries found"
  else
    .ok entries
where
  go : List (List (List Char)) → Except String (List (Range α))
    | [] => .ok []
    | fields :: rest => do
      let first ← entry fields
      let others ← go rest
      pure (match first with
        | some range => range :: others
        | none => others)

/-- A range of `value` over the code points `field` names. -/
def rangeOf {α : Type} (field : List Char) (value : α) : Except String (Range α) := do
  let (lo, hi) ← parseCodePoints field
  pure { lo, hi, value }

/-- The value `name` stands for, or an error naming the property and the unknown name. -/
def nameValue {α : Type} (property : String) (names : List (String × α)) (name : List Char) :
    Except String α :=
  match lookupName names name with
  | some value => .ok value
  | none => .error s!"unknown {property} value: {String.ofList name}"

def malformed (fields : List (List Char)) : String :=
  s!"malformed line: {String.intercalate ";" (fields.map String.ofList)}"

/-! ## The three properties -/

/-- The `Grapheme_Cluster_Break` entries of `GraphemeBreakProperty.txt`, in file order. -/
def parseGcb (text : String) : Except String (List (Range GCB)) :=
  parseEntries "Grapheme_Cluster_Break" text fun
    | [codePoints, name] => do
      let value ← nameValue "Grapheme_Cluster_Break" gcbNames name
      some <$> rangeOf codePoints value
    | fields => .error (malformed fields)

/--
The `Extended_Pictographic` entries of `emoji-data.txt`, in file order, each
with value `true`. Lines of the file's other emoji properties are skipped.
-/
def parseExtPict (text : String) : Except String (List (Range Bool)) :=
  parseEntries "Extended_Pictographic" text fun
    | [codePoints, property] =>
      if property == "Extended_Pictographic".toList then
        some <$> rangeOf codePoints true
      else
        .ok none
    | fields => .error (malformed fields)

/--
The `Indic_Conjunct_Break` entries of `DerivedCoreProperties.txt`, in file
order. Only lines whose second field is exactly `InCB` are read, with the value
in the third field; lines of the file's other properties are skipped.
-/
def parseIncb (text : String) : Except String (List (Range InCB)) :=
  parseEntries "Indic_Conjunct_Break" text fun
    | [codePoints, property, name] =>
      if property == "InCB".toList then do
        let value ← nameValue "Indic_Conjunct_Break" incbNames name
        some <$> rangeOf codePoints value
      else
        .ok none
    | fields@(_ :: property :: _) =>
      if property == "InCB".toList then .error (malformed fields) else .ok none
    | fields => .error (malformed fields)

/-! ## From entries to tables -/

/-- Inserts `range` into `sorted`, which is sorted by `lo`, keeping it sorted. -/
def insertByLo {α : Type} (range : Range α) : List (Range α) → List (Range α)
  | [] => [range]
  | r :: rest => if range.lo ≤ r.lo then range :: r :: rest else r :: insertByLo range rest

/-- `entries` sorted by `lo`. -/
def sortByLo {α : Type} (entries : List (Range α)) : List (Range α) :=
  entries.foldr insertByLo []

/--
Joins `current` with the ranges after it, which are sorted by `lo` and start no
earlier than `current`. Ranges that touch or overlap with the same value become
one range; ranges that overlap with different values are an error, because the
file would then give a code point two values.
-/
def mergeFrom {α : Type} [BEq α] [Repr α] (current : Range α) :
    List (Range α) → Except String (List (Range α))
  | [] => .ok [current]
  | next :: rest =>
    if next.lo ≤ current.hi then
      if current.value == next.value then
        mergeFrom { current with hi := max current.hi next.hi } rest
      else
        .error s!"code point {next.lo} has two values: {repr current.value} and {repr next.value}"
    else if next.lo == current.hi + 1 && current.value == next.value then
      mergeFrom { current with hi := next.hi } rest
    else
      (current :: ·) <$> mergeFrom next rest

/--
The range list the generator writes: `entries` sorted by `lo`, with
neighbouring ranges of equal value joined. Fails if two entries give one code
point different values.
-/
def normalize {α : Type} [BEq α] [Repr α] (entries : List (Range α)) :
    Except String (List (Range α)) :=
  match sortByLo entries with
  | [] => .ok []
  | first :: rest => mergeFrom first rest

/--
One value for each code point U+0000..U+10FFFF, written straight from the
file's entries: `default` where no entry lists the code point. Fails if two
entries give one code point different values. It shares no code with
`normalize` or the range lookup, so it can serve as the reference those are
checked against.
-/
def paint {α : Type} [BEq α] [Repr α] (default : α) (entries : List (Range α)) :
    Except String (Array α) := do
  let mut values : Array (Option α) := Array.replicate (maxCodePoint + 1) none
  for range in entries do
    for n in [range.lo:range.hi + 1] do
      match values[n]? with
      | some (some old) =>
        if !(old == range.value) then
          throw s!"code point {n} has two values: {repr old} and {repr range.value}"
      | some none => values := values.set! n (some range.value)
      | none => throw s!"code point past U+10FFFF: {n}"
  return values.map (·.getD default)

/-! ## The digest list -/

/-- One `sha256sum` line: 64 lowercase hex digits, two spaces, then the path. -/
def digestLinePath? (line : List Char) : Option (List Char) :=
  let digest := line.take 64
  let isLowerHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')
  match line.drop 64 with
  | ' ' :: ' ' :: path =>
    if digest.length == 64 && digest.all isLowerHex && !path.isEmpty then some path else none
  | _ => none

/--
Checks that `SHA256SUMS` lists exactly the files in `digestFiles`, each once,
one well-formed line each. `sha256sum --check` checks only the lines it is
given, so a list missing a file would leave that file unchecked.
-/
def checkDigestList (sha256sums : String) : Except String Unit := do
  let lines := (splitOnChar '\n' sha256sums.toList).filter (!·.isEmpty)
  let paths ← lines.mapM fun line =>
    match digestLinePath? line with
    | some path => .ok path
    | none => .error s!"malformed SHA256SUMS line: {String.ofList line}"
  let expected := digestFiles.map String.toList
  if paths.length != expected.length then
    .error s!"SHA256SUMS lists {paths.length} files; expected {expected.length}"
  else if expected.all (fun file => paths.count file == 1) then
    .ok ()
  else
    .error s!"SHA256SUMS must list each of: {String.intercalate ", " digestFiles}"

end SegmentationDev.TableGen
