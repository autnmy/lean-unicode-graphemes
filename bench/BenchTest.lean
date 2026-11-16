import Bench.Inputs
import BenchTest.InputsAreFourNamed
import BenchTest.InputsAsciiIsPlain
import BenchTest.InputsMixedHasEveryFeature
import BenchTest.InputsEmojiHasEveryFeature
import BenchTest.FirstDifferenceAtStart
import BenchTest.FirstDifferenceIsFirst
import BenchTest.FirstDifferenceEarliest
import BenchTest.FirstDifferenceLengthMismatch
import BenchTest.FirstDifferenceOursIsPrefix
import BenchTest.FirstDifferenceTheirsIsPrefix
import BenchTest.FirstDifferenceEmptyCluster
import BenchTest.FirstDifferenceEqualLists
import BenchTest.CheckAllNamesLaterInput
import BenchTest.CheckAllFirstInputInOrder
import BenchTest.FirstDifferenceFastIsPrefix
import BenchTest.FirstDifferenceFastEmptyCluster
import BenchTest.FirstDifferenceFastLonger
import BenchTest.FirstDifferenceFastExtraCluster
import BenchTest.CheckAllOnlyFastDiffers
import BenchTest.CheckAllOnlyFastDiffersLater
import BenchTest.CheckAllOnlyOursDiffers
import BenchTest.CheckAllOnlyTheirsDiffers
import BenchTest.CheckAllAllAgree
import BenchTest.ExitCodeFor
import BenchTest.SummarizeStats
import BenchTest.ReportRendering
import BenchTest.MeetsPassMark
import BenchTest.MeetsPassMarkAtMax
import BenchTest.MeetsPassMarkAboveMax
import BenchTest.MeetsPassMarkAtMaxWrongFields
import BenchTest.MeetsPassMarkAboveMaxWrongRules
import BenchTest.ReportPassMarkLines
import BenchTest.ReportLargeMixedPeaks
import BenchTest.ReportFastColumnsGuards
import BenchTest.ReportFastColumns
import BenchTest.OursIsReference
import BenchTest.FastIsSlice
import BenchTest.FastClustersCrLf

/-!
# Benchmark test driver

`lake test` in `bench/` builds and runs this executable. The imported test modules hold
theorems checked when they are built, so a false one stops the build. The checks below run
at run time instead, because they read the 10 MiB input, which is far too large for the kernel.
A failed runtime check makes `main` exit with status 1.
-/

namespace BenchTest

/-- A named runtime check: the name is printed so a failure says what broke. -/
structure RuntimeCheck where
  name : String
  passed : Bool

/-- True when no character of `text` is U+0000 or a surrogate code point. -/
def hasOnlyValidNonNulChars (text : String) : Bool :=
  text.all fun (c : Char) => c.toNat != 0 && !(0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF)

def inputRuntimeChecks : List RuntimeCheck :=
  let first := Bench.inputs Bench.fixedSeed
  let second := Bench.inputs Bench.fixedSeed
  let large := Bench.input Bench.fixedSeed .largeMixed
  [ { name := "the same seed gives the same text for every input",
      passed := first.map (·.text) == second.map (·.text) },
    { name := "the large input holds at least 10000000 bytes",
      passed := large.text.utf8ByteSize ≥ 10000000 },
    { name := "no input holds U+0000 or a surrogate",
      passed := first.all fun i => hasOnlyValidNonNulChars i.text },
    { name := "the large input mixes ASCII, Hangul and emoji",
      passed := large.text.any (fun (c : Char) => c.toNat < 0x80) &&
        large.text.any (fun (c : Char) => 0xAC00 ≤ c.toNat && c.toNat ≤ 0xD7A3) &&
        large.text.any (fun (c : Char) => 0x1F300 ≤ c.toNat && c.toNat ≤ 0x1FAFF) } ]

end BenchTest

open BenchTest in
def main : IO UInt32 := do
  let mut failures := 0
  for check in inputRuntimeChecks do
    if check.passed then
      IO.println s!"PASS {check.name}"
    else
      IO.eprintln s!"FAIL {check.name}"
      failures := failures + 1
  let total := inputRuntimeChecks.length
  if failures == 0 then
    IO.println s!"{total} checks passed"
    return 0
  else
    IO.eprintln s!"{failures} of {total} checks failed"
    return 1
