import Segmentation
import SegmentationTest.Statements
import SegmentationTest.Range
import SegmentationTest.RangeLookupBoundaries
import SegmentationTest.«RangeLookupBoundaries.2»
import SegmentationTest.RangeLookupEmptyAndSingle
import SegmentationTest.Ucd
import SegmentationTest.ParseGcbRejectsOutOfRange
import SegmentationTest.ParseGcbRejectsUnknownName
import SegmentationTest.ParseIncbRejectsUnknownValue
import SegmentationTest.CheckDigestListRejectsUnexpectedPath
import SegmentationTest.CheckDigestListRejectsMissingEntry
import SegmentationTest.ParseGcbUnknownName
import SegmentationTest.ParseGcbOutOfRange
import SegmentationTest.ParseIncbOtherProperties
import SegmentationTest.ParseExtPictEmpty
import SegmentationTest.NormalizeConflictingOverlap
import SegmentationTest.CheckDigestListMissingEntry
import SegmentationTest.Tables
import SegmentationTest.RenderAllRejectsCommentClose
import SegmentationTest.PropsGcbSpotChecks
import SegmentationTest.PropsIncbExtPictSpotChecks
import SegmentationTest.PropsDefaults
import SegmentationTest.GcbOfByNumber
import SegmentationTest.PropsGraphemeClusterBreakValues
import SegmentationTest.PropsIndicConjunctBreakValues
import SegmentationTest.PropsExtendedPictographic
import SegmentationTest.PropsLastCodePoint
import SegmentationTest.GcbOfSurrogates
import SegmentationTest.NumericLookupsMatchProps
import SegmentationTest.DataChecks

/-!
# Test driver

`lake test` builds and runs this executable. A failed `#guard` stops the build,
and a failed runtime check makes `main` exit with status 1, so either kind of
failure turns `lake test` red. `SegmentationTest.Statements` holds compile-time
checks of the theorem statements in `Segmentation.Statements`: importing it here
makes `lake test` elaborate it, so a failed check stops the build too.
`SegmentationTest.DataChecks` holds the checks that read the UCD files at run
time; `main` runs them after the pure checks and counts any exception as a
failure.
-/

namespace SegmentationTest

#guard Segmentation.unicodeVersion == "18.0.0"
#guard Segmentation.uax29Revision == 49

/-- A named runtime check: the name is printed so a failure says what broke. -/
structure Check where
  name : String
  passed : Bool

def checks : List Check := [
  { name := "Unicode version is 18.0.0",
    passed := Segmentation.unicodeVersion == "18.0.0" },
  { name := "UAX #29 revision is 49",
    passed := Segmentation.uax29Revision == 49 }
]

end SegmentationTest

open SegmentationTest SegmentationTest.DataChecks in
def main : IO UInt32 := do
  let mut failures := 0
  for check in checks do
    if check.passed then
      IO.println s!"PASS {check.name}"
    else
      IO.eprintln s!"FAIL {check.name}"
      failures := failures + 1
  for check in dataChecks do
    match ← runDataCheck check with
    | none => IO.println s!"PASS {check.name}"
    | some reason =>
      IO.eprintln s!"FAIL {check.name}: {reason}"
      failures := failures + 1
  let total := checks.length + dataChecks.length
  if failures == 0 then
    IO.println s!"{total} checks passed"
    return 0
  else
    IO.eprintln s!"{failures} of {total} checks failed"
    return 1
