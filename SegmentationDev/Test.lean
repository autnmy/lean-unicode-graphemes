import Segmentation
import SegmentationDev.Test.Statements
import SegmentationDev.Test.RangeLookupBoundaries
import SegmentationDev.Test.RangeLookupEmptyAndSingle
import SegmentationDev.Test.Ucd
import SegmentationDev.Test.Tables
import SegmentationDev.Test.RenderAllRejectsCommentClose
import SegmentationDev.Test.GcbOfByNumber
import SegmentationDev.Test.PropsGraphemeClusterBreakValues
import SegmentationDev.Test.PropsIndicConjunctBreakValues
import SegmentationDev.Test.PropsExtendedPictographic
import SegmentationDev.Test.PropsLastCodePoint
import SegmentationDev.Test.NumericLookupsMatchProps
import SegmentationDev.Test.DataChecks
import SegmentationDev.Test.GraphemesEnds
import SegmentationDev.Test.GraphemesCoreStubProps
import SegmentationDev.Test.GraphemesAgreesWithCore
import SegmentationDev.Test.BoundariesAgreesWithCore
import SegmentationDev.Test.GraphemesControlRules
import SegmentationDev.Test.GraphemesHangulRules
import SegmentationDev.Test.GraphemesExtendPrependRules
import SegmentationDev.Test.GraphemesConjunctRule
import SegmentationDev.Test.GraphemesEmojiZwjRule
import SegmentationDev.Test.GraphemesRegionalIndicatorRules
import SegmentationDev.Test.GraphemesCrLfAfterLoneCr
import SegmentationDev.Test.GraphemesControlRulesWinOverJoinRules
import SegmentationDev.Test.GraphemesGb9cReadsIncbNotGcb
import SegmentationDev.Test.GraphemesGb9cStarIsIncbExtend
import SegmentationDev.Test.GraphemesGb9cClearedByOtherCodePoint
import SegmentationDev.Test.GraphemesGb11DisarmedBySecondZwj
import SegmentationDev.Test.GraphemesGb11NeedsPictographBeforeZwj
import SegmentationDev.Test.GraphemeBreakTestFile
import SegmentationDev.Test.GraphemeBreakTestFileTests
import SegmentationDev.Test.GraphemesPartition
import SegmentationDev.Test.RangeScanAndSorted
import SegmentationDev.Test.TableLookupMatchesScan
import SegmentationDev.Test.ScanInvariants
import SegmentationDev.Test.GraphemesRules
import SegmentationDev.Test.AxiomChecker
import SegmentationDev.Test.AllowedAxiomsList
import SegmentationDev.Test.DisallowedAxioms
import SegmentationDev.Test.AssertAxiomsRejectsForeignAxiom
import SegmentationDev.Test.AssertAxiomsPrintsHeadlineAxioms
import SegmentationDev.Test.HeadlineAxioms
import SegmentationDev.Test.AxiomGateSelfTest
import SegmentationDev.Test.ForbiddenWordsList
import SegmentationDev.Test.FindForbiddenWords
import SegmentationDev.Test.FindForbiddenStringForms
import SegmentationDev.Test.FindForbiddenScansInterpolation
import SegmentationDev.Test.FindForbiddenProse
import SegmentationDev.Test.PropsTable
import SegmentationDev.Test.SliceAgrees

/-!
# Test driver

`lake test` builds and runs this executable. A failed `#guard` stops the build,
and a failed runtime check makes `main` exit with status 1, so either kind of
failure turns `lake test` red. `SegmentationDev.Test.Statements` holds compile-time
checks of the theorem statements in `Segmentation.Statements`: importing it here
makes `lake test` elaborate it, so a failed check stops the build too.
`SegmentationDev.Test.DataChecks` holds the checks that read the UCD files at run
time; `main` runs them after the pure checks and counts any exception as a
failure.
-/

namespace SegmentationDev.Test

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

end SegmentationDev.Test

open SegmentationDev.Test SegmentationDev.Test.DataChecks in
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
