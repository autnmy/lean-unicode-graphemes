import Segmentation
import SegmentationTest.RulesOrder
import SegmentationTest.H1aSignature
import SegmentationTest.H1bSignature
import SegmentationTest.H2Signature
import SegmentationTest.H2PrimeSignature
import SegmentationTest.H1aJoinHolds
import SegmentationTest.H1aRejectsDrop
import SegmentationTest.H2RejectsMissingEndCut
import SegmentationTest.Statements.RuleNames
import SegmentationTest.Statements.RuleVerdicts
import SegmentationTest.Statements.H1aSignature
import SegmentationTest.Statements.H1bEmptyCluster
import SegmentationTest.Statements.H2Signature
import SegmentationTest.Statements.H2PrimeEmpty
import tests.Statements.RulesOrder
import tests.Statements.GB9cRevision49
import tests.Statements.H1aParameters
import tests.Statements.H2ParameterOrder
import tests.Statements.H2PrimeParameterOrder

/-!
# Test driver

`lake test` builds and runs this executable. A failed `#guard` stops the build,
and a failed runtime check makes `main` exit with status 1, so either kind of
failure turns `lake test` red. The imported modules hold compile-time checks of
the theorem statements in `Segmentation.Statements`: importing them here makes
`lake test` elaborate them, so a failed check stops the build too.
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

open SegmentationTest in
def main : IO UInt32 := do
  let mut failures := 0
  for check in checks do
    if check.passed then
      IO.println s!"PASS {check.name}"
    else
      IO.eprintln s!"FAIL {check.name}"
      failures := failures + 1
  if failures == 0 then
    IO.println s!"{checks.length} checks passed"
    return 0
  else
    IO.eprintln s!"{failures} of {checks.length} checks failed"
    return 1
