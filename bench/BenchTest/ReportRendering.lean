import Bench.Inputs
import Bench.Report

/-!
Checks of the benchmark's statistics and of the results file the CI job uploads. The timings
themselves depend on the machine and are not checked; these check what the file states.
-/

namespace BenchTest.ReportRendering

open Bench

/-- True when `part` occurs in `text`. -/
def reportMentions (text part : String) : Bool :=
  (text.splitOn part).length > 1

-- An even count takes the lower of the two middle samples.
#guard summarize [40, 10, 30, 20] == { median := 20, min := 10, max := 40, count := 4 }
#guard summarize [7] == { median := 7, min := 7, max := 7, count := 1 }
#guard summarize [] == { median := 0, min := 0, max := 0, count := 0 }

def sampleRun : RunMeta :=
  { machine := "AMD EPYC 7763 64-Core Processor, 4 cores",
    toolchain := "leanprover/lean4:v4.36.0-rc2",
    oursCommit := "0123456789abcdef0123456789abcdef01234567",
    theirsCommit := "44228db53c81aaaaaaaaaaaaaaaaaaaaaaaaaaaa" }

def sampleRow (name : String) : ResultRow :=
  { input := name, callsPerSample := 100,
    ours := summarize [300, 100, 200], theirs := summarize [30, 10, 20],
    fast := summarize [25, 5, 15],
    baselinePeakKb := 1111, oursPeakKb := 2222, theirsPeakKb := 3333, fastPeakKb := 4444 }

def sampleTable : String :=
  renderTable sampleRun (Bench.InputKind.all.map fun k => sampleRow k.name)

#guard Bench.InputKind.all.all fun k => reportMentions sampleTable s!"| {k.name} |"
#guard reportMentions sampleTable
  "| plain-ascii | 3 | 100 | 200 | 100-300 | 20 | 10-30 | 15 | 5-25 | 1111 | 2222 | 3333 | 4444 |"
#guard ["This library median", "This library min-max", "UnicodeExtra median",
    "UnicodeExtra min-max", "Fast median", "Fast min-max", "Samples", "Baseline peak",
    "This library peak", "UnicodeExtra peak", "Fast peak"].all (reportMentions sampleTable)
-- Every input gets a pass-mark line, and the list ends with the large-mixed peaks.
#guard Bench.InputKind.all.all fun k =>
  reportMentions sampleTable
    s!"- {k.name}: fast median 15 ns, UnicodeExtra min-max 10-30 ns, fast median at most UnicodeExtra max: yes"
#guard reportMentions sampleTable "- Peak memory on large-mixed: fast 4444 KiB, UnicodeExtra 3333 KiB"
#guard reportMentions sampleTable sampleRun.machine
#guard reportMentions sampleTable sampleRun.toolchain
#guard reportMentions sampleTable sampleRun.oursCommit
#guard reportMentions sampleTable sampleRun.theirsCommit
#guard reportMentions sampleTable memoryMethod
#guard reportMentions memoryMethod "includes building the input"
-- One table: exactly one header separator line.
#guard ((sampleTable.splitOn "\n").filter (·.startsWith "|---")).length == 1
-- No wording that judges the result.
#guard ["faster", "slower"].all fun w => !reportMentions sampleTable w

/-- A row whose UnicodeExtra median, min and max all differ, with the given fast median. -/
def passMarkRow (input : String) (fastMedian : Nat) : ResultRow :=
  { input, callsPerSample := 7,
    ours := { median := 41, min := 40, max := 42, count := 3 },
    theirs := { median := 300, min := 200, max := 500, count := 3 },
    fast := { median := fastMedian, min := 11, max := 990, count := 3 },
    baselinePeakKb := 61, oursPeakKb := 62, theirsPeakKb := 63, fastPeakKb := 64 }

-- plain-ascii sits exactly at the mark and reads yes; emoji is one nanosecond above and reads
-- no. Each line must carry its own input's answer, as in the issue's example
-- `- plain-ascii: fast median 9000 ns, UnicodeExtra min-max 9254-10788 ns, fast median at most
-- UnicodeExtra max: yes`.
#guard
  let lines := (renderTable sampleRun [passMarkRow "plain-ascii" 500, passMarkRow "emoji" 501]
    ).splitOn "\n"
  lines.contains ("- plain-ascii: fast median 500 ns, UnicodeExtra min-max 200-500 ns, " ++
      "fast median at most UnicodeExtra max: yes") &&
    lines.contains ("- emoji: fast median 501 ns, UnicodeExtra min-max 200-500 ns, " ++
      "fast median at most UnicodeExtra max: no")

-- With a pass-mark line that reads no, the report still has one table rule line and never
-- says faster or slower.
#guard
  let text := renderTable sampleRun [passMarkRow "plain-ascii" 500, passMarkRow "large-mixed" 501]
  ((text.splitOn "\n").filter (·.startsWith "|---")).length == 1 &&
    !reportMentions text "faster" && !reportMentions text "slower" &&
    reportMentions text "Pass mark"

-- "A `large-mixed` row with baseline 1000, fast 9000 and theirs 4000 shows 9000 and 4000, and
-- never 8000 or 3000." The peak line shows both peaks as measured, and no peak minus the
-- baseline appears anywhere in the report.
#guard
  let row : ResultRow :=
    { input := "large-mixed", callsPerSample := 1,
      ours := { median := 41, min := 40, max := 42, count := 7 },
      theirs := { median := 51, min := 50, max := 52, count := 7 },
      fast := { median := 71, min := 70, max := 72, count := 7 },
      baselinePeakKb := 1000, oursPeakKb := 2000, theirsPeakKb := 4000, fastPeakKb := 9000 }
  let text := renderTable sampleRun [row]
  (text.splitOn "\n").contains
      "- Peak memory on large-mixed: fast 9000 KiB, UnicodeExtra 4000 KiB" &&
    !reportMentions text "8000" && !reportMentions text "3000"

def sampleFailure : String :=
  renderBuildFailure sampleRun
    { failedTarget := "lean-unicode-graphemes/Segmentation", errorTail := "error: unknown constant" }

#guard reportMentions sampleFailure "cannot build together"
#guard reportMentions sampleFailure "lean-unicode-graphemes/Segmentation"
#guard reportMentions sampleFailure "error: unknown constant"
#guard reportMentions sampleFailure sampleRun.toolchain
#guard reportMentions sampleFailure sampleRun.theirsCommit
-- No numbers: no table and no measurement columns.
#guard !reportMentions sampleFailure "|"
#guard !reportMentions sampleFailure "median"

end BenchTest.ReportRendering
