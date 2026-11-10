import Segmentation

/-!
# Test driver

`lake test` builds and runs this executable. A failed `#guard` stops the build,
and a failed runtime check makes `main` exit with status 1, so either kind of
failure turns `lake test` red.
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
