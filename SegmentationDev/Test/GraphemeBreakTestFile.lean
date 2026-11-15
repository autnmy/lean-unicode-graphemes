import SegmentationDev.TableGen

/-!
# Reading GraphemeBreakTest.txt

Pure functions for the conformance check against Unicode's own test file,
`data/ucd/18.0.0/auxiliary/GraphemeBreakTest.txt`. A test line reads like

    ÷ 000D × 000A ÷	#  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) × [3.0] ...

where `÷` (U+00F7) marks a break and `×` (U+00D7) marks no break. The expected clusters come
only from these markers, never from the segmenter, so the comparison can disagree with it.

The parser is strict: a line it cannot read is an error naming its line number, never skipped,
because a skipped line would let the check pass while comparing less than the whole file. The
helpers work on `List Char` with structural recursion, like `SegmentationDev.TableGen.Ucd`, so
`decide` can evaluate them in the tests.
-/

namespace SegmentationDev.Test.GraphemeBreakTestFile

open SegmentationDev.TableGen

/-- One test line of the file: its physical line number (from 1), its code points, and the
clusters the file's markers give them. -/
structure GraphemeBreakCase where
  line : Nat
  codePoints : List Nat
  expected : List (List Nat)
  deriving Repr

/-- The case for test line `line` whose markers give the clusters `expected`. The code points
are the clusters joined, so the two can never disagree. -/
def GraphemeBreakCase.ofClusters (line : Nat) (expected : List (List Nat)) : GraphemeBreakCase :=
  { line, codePoints := expected.flatten, expected }

/-- How many test lines GraphemeBreakTest.txt holds for Unicode 18.0.0. -/
def expectedLineCount : Nat := 853

/-- The marker character for a break. -/
def breakMarker : Char := '÷'

/-- The marker character for no break. -/
def joinMarker : Char := '×'

/-- Whether the token `token` is a break marker (`some true`), a no-break marker
(`some false`), or not a marker (`none`). -/
def markerBreaks? (token : List Char) : Option Bool :=
  if token == [breakMarker] then some true
  else if token == [joinMarker] then some false
  else none

/-- The code point a hex token names, when it is a valid `Char`. Surrogates and values past
U+10FFFF are refused, because `Char.ofNat` would quietly turn them into U+0000. -/
def codePoint? (token : List Char) : Option Nat := do
  let n ← parseHex? token
  if decide n.isValidChar then some n else none

/--
Reads the tokens after the leading `÷`: alternately a code point and a marker, the last marker
a `÷`. `cluster` holds the code points of the open cluster and `clusters` the closed ones, both
reversed.
-/
def readClusters : List (List Char) → List Nat → List (List Nat) → Option (List (List Nat))
  | [hex, marker], cluster, clusters => do
    let cp ← codePoint? hex
    if (← markerBreaks? marker) then some ((cp :: cluster).reverse :: clusters).reverse
    else none
  | hex :: marker :: rest, cluster, clusters => do
    let cp ← codePoint? hex
    if (← markerBreaks? marker) then readClusters rest [] ((cp :: cluster).reverse :: clusters)
    else readClusters rest (cp :: cluster) clusters
  | _, _, _ => none

/-- The expected clusters of one test line's content, comment already dropped. -/
def parseClusters (content : List Char) : Option (List (List Nat)) :=
  match (splitOnChar ' ' content).filter (· ≠ []) with
  | first :: rest => if markerBreaks? first == some true then readClusters rest [] [] else none
  | [] => none

/-- The test cases of `lines`, the first of which is physical line `line`. Comment-only and
blank lines are not test lines. -/
def parseLines (line : Nat) : List (List Char) → Except String (List GraphemeBreakCase)
  | [] => .ok []
  | chars :: rest =>
    let content := trim (dropComment chars)
    if content.isEmpty then
      parseLines (line + 1) rest
    else
      match parseClusters content with
      | some expected =>
        (.ofClusters line expected :: ·) <$> parseLines (line + 1) rest
      | none =>
        .error s!"line {line} is not a GraphemeBreakTest.txt test line: {String.ofList content}"

/-- Every test line of the text of GraphemeBreakTest.txt, in file order. -/
def parseTestFile (text : String) : Except String (List GraphemeBreakCase) :=
  parseLines 1 (splitOnChar '\n' text.toList)

/-- A non-empty string of decimal digits, read as a number. -/
def parseDecimal? (chars : List Char) : Option Nat :=
  if chars.isEmpty then none else go chars 0
where
  go : List Char → Nat → Option Nat
    | [], acc => some acc
    | c :: rest, acc =>
      if c.isDigit then go rest (acc * 10 + (c.toNat - '0'.toNat)) else none

/-- The trailer line that states how many test lines the file has. -/
def lineCountPrefix : List Char := "# Lines:".toList

/-- The count stated by the file's `# Lines: N` trailer, if it has one. -/
def statedLineCount (text : String) : Option Nat :=
  ((splitOnChar '\n' text.toList).filterMap fun line =>
    let content := trim line
    if lineCountPrefix.isPrefixOf content then
      parseDecimal? (trim (content.drop lineCountPrefix.length))
    else none).head?

/--
Fails unless the parser read as many test lines as the file states, and that number is 853.
Both are needed: the trailer catches a parser that drops lines, and the fixed count catches a
truncated file whose trailer was edited to agree.
-/
def checkCounts (parsed : Nat) (stated : Option Nat) : Except String Unit :=
  match stated with
  | none => .error "the file states no line count: its \"# Lines:\" trailer is missing"
  | some stated =>
    if parsed != stated then
      .error s!"parsed {parsed} test lines, but the file states {stated}"
    else if parsed != expectedLineCount then
      .error s!"the file has {parsed} test lines, expected {expectedLineCount}"
    else
      .ok ()

/-- The line numbers, in file order, of every case whose clusters `segment` gets wrong. There is
no cap: every differing line is reported. -/
def mismatches (segment : List Nat → List (List Nat)) (cases : List GraphemeBreakCase) :
    List Nat :=
  cases.filterMap fun c => if segment c.codePoints == c.expected then none else some c.line

/-! ## The generated case module

The kernel cannot read a file, so a theorem about the test file needs its cases as Lean terms.
`lake exe gen-tables` writes them to `casesModulePath`, and `lake test` and CI fail when that
module differs from what `renderCasesModule` makes of the file now. Only the parsed cases are
written: most of the file's bytes are comments, which a kernel proof would otherwise walk
through.
-/

/-- The generated module holding every test line of GraphemeBreakTest.txt, relative to the
package root. -/
def casesModulePath : System.FilePath := "SegmentationDev" / "Test" / "GraphemeBreakTestData.lean"

/-- `codePoints` as a Lean list literal of hexadecimal numbers. -/
def renderCodePoints (codePoints : List Nat) : String :=
  "[" ++ ", ".intercalate (codePoints.map hex) ++ "]"

/-- One case as a Lean term. Only the line and the clusters are written: `ofClusters` rebuilds
the code points from the clusters, as the parser does. -/
def renderCase (c : GraphemeBreakCase) : String :=
  let clusters := "[" ++ ", ".intercalate (c.expected.map renderCodePoints) ++ "]"
  s!"  .ofClusters {c.line} {clusters}"

/--
The text of the generated case module, from the text of `LICENSE.txt` and of
GraphemeBreakTest.txt. Fails unless the file parses and passes `checkCounts`, so a truncated
file never becomes the data a proof reads, and fails if the licence cannot be put in a comment.
-/
def renderCasesModule (licence text : String) : Except String String := do
  let cases ← parseTestFile text
  checkCounts cases.length (statedLineCount text)
  let header ← licenceHeader licence
  -- The same chunking as the tables, because one long list literal is slow to elaborate.
  let pieces := chunks chunkSize cases
  let chunkName (i : Nat) := s!"casesChunk{i}"
  let renderChunk (i : Nat) (piece : List GraphemeBreakCase) :=
    s!"private def {chunkName i} : List GraphemeBreakCase := [\n" ++
    ",\n".intercalate (piece.map renderCase) ++ "\n]\n\n"
  let chunkDefs := String.join ((List.range pieces.length).zip pieces |>.map
    fun (i, piece) => renderChunk i piece)
  let joined := " ++ ".intercalate ((List.range pieces.length).map chunkName)
  pure <| header ++
    s!"-- Generated by `lake exe gen-tables` from " ++
    s!"data/ucd/{Segmentation.unicodeVersion}/auxiliary/GraphemeBreakTest.txt.\n" ++
    "-- Do not edit by hand: CI regenerates this file and fails on any difference.\n\n" ++
    "import SegmentationDev.Test.GraphemeBreakTestFile\n\n" ++
    "namespace SegmentationDev.Test.GraphemeBreakTestData\n\n" ++
    "open SegmentationDev.Test.GraphemeBreakTestFile\n\n" ++
    chunkDefs ++
    "/-- Every test line of GraphemeBreakTest.txt, in file order. -/\n" ++
    s!"def cases : List GraphemeBreakCase :=\n  {joined}\n\n" ++
    "end SegmentationDev.Test.GraphemeBreakTestData\n"

end SegmentationDev.Test.GraphemeBreakTestFile
