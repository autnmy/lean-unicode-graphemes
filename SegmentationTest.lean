import Segmentation
import SegmentationTest.Statements
import SegmentationTest.«RangeLookupBoundaries.2»
import SegmentationTest.RangeLookupEmptyAndSingle
import SegmentationTest.Ucd
import SegmentationTest.ParseIncbRejectsUnknownValue
import SegmentationTest.ParseGcbUnknownName
import SegmentationTest.ParseIncbOtherProperties
import SegmentationTest.ParseExtPictEmpty
import SegmentationTest.NormalizeConflictingOverlap
import SegmentationTest.Tables
import SegmentationTest.RenderAllRejectsCommentClose
import SegmentationTest.GcbOfByNumber
import SegmentationTest.PropsGraphemeClusterBreakValues
import SegmentationTest.PropsIndicConjunctBreakValues
import SegmentationTest.PropsExtendedPictographic
import SegmentationTest.PropsLastCodePoint
import SegmentationTest.NumericLookupsMatchProps
import SegmentationTest.DataChecks
import SegmentationTest.GraphemesEnds
import SegmentationTest.GraphemesCoreStubProps
import SegmentationTest.GraphemesAgreesWithCore
import SegmentationTest.BoundariesAgreesWithCore
import SegmentationTest.GraphemesControlRules
import SegmentationTest.GraphemesHangulRules
import SegmentationTest.GraphemesExtendPrependRules
import SegmentationTest.GraphemesConjunctRule
import SegmentationTest.GraphemesEmojiZwjRule
import SegmentationTest.GraphemesRegionalIndicatorRules
import SegmentationTest.GraphemesCrLfAfterLoneCr
import SegmentationTest.GraphemesControlRulesWinOverJoinRules
import SegmentationTest.GraphemesGb9cReadsIncbNotGcb
import SegmentationTest.GraphemesGb9cStarIsIncbExtend
import SegmentationTest.GraphemesGb9cClearedByOtherCodePoint
import SegmentationTest.GraphemesGb11DisarmedBySecondZwj
import SegmentationTest.GraphemesGb11NeedsPictographBeforeZwj
import SegmentationTest.GraphemeBreakTestFile
import SegmentationTest.GraphemeBreakTestFileTests
import SegmentationTest.GraphemesPartition
import SegmentationTest.RangeScanAndSorted
import SegmentationTest.TableLookupMatchesScan
import SegmentationTest.ScanInvariants
import SegmentationTest.ScanInvariantsScanStateOfDef
import SegmentationTest.ScanInvariantsFlagTypes
import SegmentationTest.«ScanInvariantsFlagTypes.2»
import SegmentationTest.ScanInvariantsGB11Breaks
import SegmentationTest.ScanInvariantsLinkerBroken
import SegmentationTest.ScanInvariantsLinkerTail
import SegmentationTest.ScanInvariantsRiOddThree
import SegmentationTest.«ScanInvariantsRiOddThree.2»
import SegmentationTest.ScanInvariantsRiOddFour
import SegmentationTest.«ScanInvariantsRiOddFour.2»
import SegmentationTest.ScanInvariantsZwjAfterPict
import SegmentationTest.ScanInvariantsZwjTwice
import SegmentationTest.ScanInvariants.LinkerTailExtendRun
import SegmentationTest.ScanInvariants.RiOddRestartsAfterZwj
import SegmentationTest.ScanInvariants.ZwjAfterPictExtendRun
import SegmentationTest.ScanInvariantsAxioms
import SegmentationTest.«ScanInvariantsAxioms.2»
import SegmentationTest.ScanInvariantsBoundaryTypes
import SegmentationTest.ScanInvariantsDecisionTypes
import SegmentationTest.ScanInvariantsCRLF
import SegmentationTest.ScanInvariantsCRLFNoBoundary
import SegmentationTest.ScanInvariantsGB11NoBoundary
import SegmentationTest.«ScanInvariantsGB11NoBoundary.2»
import SegmentationTest.ScanInvariantsGB12
import SegmentationTest.ScanInvariantsGB13
import SegmentationTest.ScanInvariantsGB13NoBoundary
import SegmentationTest.ScanInvariantsGB999Boundary
import SegmentationTest.ScanInvariants.Gb11DoubleZwjBreaks
import SegmentationTest.ScanInvariants.Gb13NoBoundary
import SegmentationTest.ScanInvariants.Gb4BeforeGb9
import SegmentationTest.ScanInvariants.ThirdRegionalIndicatorBreaks

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
