import Segmentation
import TableGen
import SegmentationTest.GraphemeBreakTestFile
import SegmentationTest.GraphemeBreakTestLine

/-!
# Checks against the UCD files

Runtime checks that read the files under `data/ucd/<version>/`, so they run in
the test executable rather than at compile time. `lake test` runs it from the
package root.

Each check is an `IO Unit` that throws when it fails. The driver treats every
exception as a failure, so a file that cannot be read, a parse error or a tool
that cannot run turns `lake test` red instead of checking nothing.
-/

namespace SegmentationTest.DataChecks

open Segmentation Segmentation.Tables TableGen

/-- A named check that throws when it fails. -/
structure DataCheck where
  name : String
  run : IO Unit

/-- Runs `check`: `none` when it passes, else the reason it failed. -/
def runDataCheck (check : DataCheck) : IO (Option String) := do
  try
    check.run
    return none
  catch e =>
    return some (toString e)

def failWith {α : Type} (message : String) : IO α :=
  throw (IO.userError message)

/-- The text of the files the generator reads. -/
structure Sources where
  licence : String
  gcb : String
  extPict : String
  incb : String

def loadSources : IO Sources := do
  let read (file : String) : IO String := IO.FS.readFile (dataDir / file)
  return {
    licence := ← read "LICENSE.txt",
    gcb := ← read "auxiliary/GraphemeBreakProperty.txt",
    extPict := ← read "emoji/emoji-data.txt",
    incb := ← read "DerivedCoreProperties.txt" }

/-! ## Digests -/

/--
Checks the UCD files against `SHA256SUMS` with `program`, run in `dataDir`.
`checkDigestList` first makes sure the list names exactly the expected files,
because `sha256sum --check` checks only the lines it is given.
-/
def checkDigests (program : String) : IO Unit := do
  IO.ofExcept (checkDigestList (← IO.FS.readFile (dataDir / "SHA256SUMS")))
  let out ← IO.Process.output
    { cmd := program, args := #["--check", "--strict", "SHA256SUMS"], cwd := some dataDir }
  if out.exitCode != 0 then
    failWith s!"{program} exited with {out.exitCode}: {out.stdout}{out.stderr}"

/-! ## The exhaustive table check -/

/-- The value of each property for every code point U+0000..U+10FFFF, read from the files. -/
structure Reference where
  gcb : Array GCB
  extPict : Array Bool
  incb : Array InCB

/--
The reference values, painted straight from the parsed file entries. They do
not pass through `normalize`, the generated modules or the range lookup, which
are what the exhaustive check tests.
-/
def loadReference : IO Reference := do
  let s ← loadSources
  return {
    gcb := ← IO.ofExcept (parseGcb s.gcb >>= paint .Other),
    extPict := ← IO.ofExcept (parseExtPict s.extPict >>= paint false),
    incb := ← IO.ofExcept (parseIncb s.incb >>= paint .None) }

/-- The properties `ref` gives code point `n`, or `none` past its end. -/
def Reference.props? (ref : Reference) (n : Nat) : Option Props := do
  return { gcb := ← ref.gcb[n]?, extPict := ← ref.extPict[n]?, incb := ← ref.incb[n]? }

/-- Every code point U+0000..U+10FFFF, surrogates included. -/
def codePointCount : Nat := maxCodePoint + 1

/-- The code points a `Char` can hold: all of them but the 0x800 surrogates. -/
def scalarValueCount : Nat := codePointCount - 0x800

/-- How many values a comparison made, and the first few that differed. -/
structure Comparison where
  compared : Nat := 0
  mismatches : Array Nat := #[]

/-- How many mismatching code points a failure reports. -/
def reportedMismatches : Nat := 10

def Comparison.record (c : Comparison) (n : Nat) (same : Bool) : Comparison :=
  { compared := c.compared + 1,
    mismatches := if same || c.mismatches.size ≥ reportedMismatches then c.mismatches
      else c.mismatches.push n }

/-- The numeric lookups against `ref` for every code point, surrogates included. -/
def compareNumbers (ref : Reference) : Comparison := Id.run do
  let mut result : Comparison := {}
  for n in [0:codePointCount] do
    let looked : Props := { gcb := gcbOf n, extPict := extPictOf n, incb := incbOf n }
    result := result.record n (ref.props? n == some looked)
  return result

/--
`Tables.props` against `ref` for every `Char`. A `Char` is built only from a
valid scalar value, never with `Char.ofNat`, which would turn each surrogate
into U+0000 and check that one code point 2048 times.
-/
def compareChars (ref : Reference) : Comparison := Id.run do
  let mut result : Comparison := {}
  for n in [0:codePointCount] do
    if h : n.isValidChar then
      result := result.record n (ref.props? n == some (props (Char.ofNatAux n h)))
  return result

def checkComparison (what : String) (expectedCount : Nat) (c : Comparison) : IO Unit := do
  if c.compared != expectedCount then
    failWith s!"{what}: compared {c.compared}, expected {expectedCount}"
  if !c.mismatches.isEmpty then
    failWith s!"{what}: differs from the UCD files at {c.mismatches.toList.map TableGen.hex}"
  IO.println s!"  {what}: {c.compared} compared, all equal to the UCD files"

def checkExhaustive : IO Unit := do
  let ref ← loadReference
  checkComparison "code points by number" codePointCount (compareNumbers ref)
  checkComparison "characters through Tables.props" scalarValueCount (compareChars ref)

/--
Fixed values the reference must give, written out here so a parser bug shared
by the generator and the reference cannot pass unnoticed.
-/
def checkReferenceSpots : IO Unit := do
  let ref ← loadReference
  let expected : List (String × Bool) := [
    ("U+1F1E6 is Regional_Indicator", ref.gcb[0x1F1E6]? == some .RI),
    ("U+0300 is Extend", ref.gcb[0x0300]? == some .Extend),
    ("U+0903 is SpacingMark", ref.gcb[0x0903]? == some .SpacingMark),
    ("U+094D is InCB=Linker", ref.incb[0x094D]? == some .Linker),
    ("U+0915 is InCB=Consonant", ref.incb[0x0915]? == some .Consonant),
    ("U+00A9 is Extended_Pictographic", ref.extPict[0x00A9]? == some true)
  ]
  for (name, holds) in expected do
    if !holds then failWith s!"reference value wrong: {name}"

/-! ## The committed tables -/

def renderFromSources : IO (List (System.FilePath × String)) := do
  let s ← loadSources
  IO.ofExcept (renderAll s.licence s.gcb s.extPict s.incb)

/-- Each committed table module equals, byte for byte, what the generator writes now. -/
def checkCommittedTables : IO Unit := do
  for (path, contents) in ← renderFromSources do
    if (← IO.FS.readFile path) != contents then
      failWith s!"{path} differs from `lake exe gen-tables` output; rerun the generator"

/-- The path of Unicode's grapheme cluster conformance test file. -/
def graphemeBreakTestPath : System.FilePath := dataDir / "auxiliary/GraphemeBreakTest.txt"

/-- The case module `lake exe gen-tables` writes now from GraphemeBreakTest.txt. -/
def renderCasesFromSource : IO String := do
  IO.ofExcept (GraphemeBreakTestFile.renderCasesModule
    (← IO.FS.readFile (dataDir / "LICENSE.txt")) (← IO.FS.readFile graphemeBreakTestPath))

/-- Fails unless `committed` equals, byte for byte, the case module the generator writes now. -/
def checkCasesModuleText (committed : String) : IO Unit := do
  if committed != (← renderCasesFromSource) then
    failWith s!"{GraphemeBreakTestFile.casesModulePath} differs from `lake exe gen-tables` output; rerun the generator"

/-- The committed case module equals what the generator writes now from GraphemeBreakTest.txt,
so a proof about it is a proof about the file's lines. -/
def checkCommittedTestData : IO Unit := do
  checkCasesModuleText (← IO.FS.readFile GraphemeBreakTestFile.casesModulePath)

/-- The committed case module with the case for test-file line 840 removed. -/
def casesModuleWithoutLine840 : IO String := do
  let committed ← IO.FS.readFile GraphemeBreakTestFile.casesModulePath
  return "\n".intercalate ((committed.splitOn "\n").filter (!·.startsWith "  .ofClusters 840 "))

/-- Each generated module starts with the licence header built from `LICENSE.txt`. -/
def checkLicenceHeaders : IO Unit := do
  let header ← IO.ofExcept (licenceHeader (← IO.FS.readFile (dataDir / "LICENSE.txt")))
  let paths := (← renderFromSources).map (·.1) ++ [GraphemeBreakTestFile.casesModulePath]
  for path in paths do
    if !(← IO.FS.readFile path).startsWith header then
      failWith s!"{path} does not start with the Unicode licence notice"

/-! ## The conformance test file -/

/--
Runs `segment` on every test line of the GraphemeBreakTest.txt at `path`. Fails unless all 853
lines were read, and names every line whose clusters differ, with no cap on how many.
-/
def checkGraphemeBreakTest (path : System.FilePath) (segment : List Nat → List (List Nat)) :
    IO Unit := do
  let text ← IO.FS.readFile path
  let cases ← IO.ofExcept (GraphemeBreakTestFile.parseTestFile text)
  IO.ofExcept (GraphemeBreakTestFile.checkCounts cases.length
    (GraphemeBreakTestFile.statedLineCount text))
  let differing := GraphemeBreakTestFile.mismatches segment cases
  if !differing.isEmpty then
    failWith s!"{differing.length} of {cases.length} lines of {path} differ, at lines {differing}"
  IO.println s!"  {path}: {cases.length} lines compared, all clusters equal to the file"

/-- A segmenter that never joins code points, so it disagrees with every line that does. -/
def splitEveryCodePoint (cps : List Nat) : List (List Nat) := cps.map ([·])

/-! ## Checks of the checks -/

/-- Fails unless `check` fails: a broken input must never read as a pass. -/
def expectFailure (check : DataCheck) : IO Unit := do
  if (← runDataCheck check).isNone then
    failWith s!"{check.name} passed, but it must fail"

def dataChecks : List DataCheck := [
  { name := "UCD files match SHA256SUMS", run := checkDigests "sha256sum" },
  { name := "digest check fails when the hashing tool cannot run",
    run := expectFailure
      { name := "missing hashing tool", run := checkDigests "segmentation-test-no-such-program" } },
  { name := "digest check fails when the hashing tool exits non-zero",
    run := expectFailure { name := "failing hashing tool", run := checkDigests "false" } },
  { name := "a missing data file fails its check",
    run := expectFailure
      { name := "missing data file",
        run := discard (IO.FS.readFile (dataDir / "segmentation-test-missing.txt")) } },
  { name := "reference values read from the UCD files", run := checkReferenceSpots },
  { name := "every code point's properties equal the UCD files", run := checkExhaustive },
  { name := "committed tables equal the generator's output", run := checkCommittedTables },
  { name := "committed tables start with the Unicode licence notice", run := checkLicenceHeaders },
  { name := "graphemes match every line of GraphemeBreakTest.txt",
    run := checkGraphemeBreakTest graphemeBreakTestPath GraphemeBreakTestLine.clusters },
  { name := "the GraphemeBreakTest.txt check fails when the file is missing",
    run := expectFailure
      { name := "missing GraphemeBreakTest.txt",
        run := checkGraphemeBreakTest (dataDir / "segmentation-test-missing.txt")
          GraphemeBreakTestLine.clusters } },
  { name := "the GraphemeBreakTest.txt check fails when clusters differ",
    run := expectFailure
      { name := "segmenter that never joins",
        run := checkGraphemeBreakTest graphemeBreakTestPath splitEveryCodePoint } },
  { name := "committed GraphemeBreakTest.txt cases equal the generator's output",
    run := checkCommittedTestData },
  { name := "the GraphemeBreakTest.txt case drift check fails when a case is missing",
    run := expectFailure
      { name := "case module without line 840",
        run := do checkCasesModuleText (← casesModuleWithoutLine840) } }
]

end SegmentationTest.DataChecks
