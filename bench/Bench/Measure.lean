import Bench.Inputs
import Bench.Report

/-!
# Timing and peak memory

Each measurement runs in a child process of its own, one input and one library per process,
because peak resident memory (`VmHWM`) is a property of the whole process: two libraries in one
process would share one peak. The parent spawns the children, reads one line from each, and
builds the results table.

A child prints one line: its peak in KiB, then its samples in nanoseconds per call, separated
by spaces. The baseline child, which only builds the input, prints its peak alone.
-/

namespace Bench

/-- What a child process measures: the input alone, or one library on it. -/
inductive Library where
  | baseline
  | ours
  | theirs
  deriving DecidableEq, Repr

namespace Library

def all : List Library := [.baseline, .ours, .theirs]

def name : Library → String
  | .baseline => "baseline"
  | .ours => "ours"
  | .theirs => "theirs"

def ofName? (name : String) : Option Library :=
  all.find? (·.name == name)

end Library

/-- The `InputKind` whose name is `name`. -/
def InputKind.ofName? (name : String) : Option InputKind :=
  InputKind.all.find? (·.name == name)

/-- How many samples to take of one input, after how many uncounted warm-up samples, and how
many calls each sample makes. A small input takes microseconds per call, below the clock's
useful resolution, so its samples time a batch of calls. -/
structure TimingPlan where
  samples : Nat
  warmups : Nat
  callsPerSample : Nat

def timingPlan : InputKind → TimingPlan
  | .largeMixed => { samples := 7, warmups := 2, callsPerSample := 1 }
  | _ => { samples := 31, warmups := 2, callsPerSample := 1000 }

/-- The KiB value of the `VmHWM:` line of a `/proc/self/status` file. -/
def parseVmHwmKb (status : String) : Option Nat :=
  (status.splitOn "\n").findSome? fun line =>
    (line.dropPrefix? "VmHWM:").bind fun rest =>
      ((rest.copy.trimAscii.copy.dropSuffix? " kB").map (·.copy)).bind String.toNat?

/-- The line a child prints. -/
def encodeMeasurement (peakKb : Nat) (samples : List Nat) : String :=
  " ".intercalate ((peakKb :: samples).map toString)

/-- The peak and samples in a child's line, or `none` when it is not such a line. -/
def decodeMeasurement (line : String) : Option (Nat × List Nat) :=
  match (line.trimAscii.copy.splitOn " ").mapM String.toNat? with
  | some (peakKb :: samples) => some (peakKb, samples)
  | _ => none

/-- This process's peak resident memory in KiB. -/
def peakResidentKb : IO Nat := do
  let status ← IO.FS.readFile "/proc/self/status"
  match parseVmHwmKb status with
  | some kb => return kb
  | none => throw (IO.userError "no VmHWM line in /proc/self/status")

/-- Times `clusterCount` on `text` and returns nanoseconds per call for each counted sample.
The text is read from a reference before every call and every result is added to a total that
is printed at the end. Without that, the compiler may compute a call once for the whole loop, or
drop a call whose result is unused. -/
def timeSamples (clusterCount : String → Nat) (text : String) (plan : TimingPlan) :
    IO (List Nat) := do
  let textRef ← IO.mkRef text
  let totalClusters ← IO.mkRef 0
  let oneSample : IO Nat := do
    let start ← IO.monoNanosNow
    for _ in [0:plan.callsPerSample] do
      let current ← textRef.get
      totalClusters.modify (· + clusterCount current)
    let stop ← IO.monoNanosNow
    return (stop - start) / plan.callsPerSample
  for _ in [0:plan.warmups] do
    discard oneSample
  let mut samples : Array Nat := #[]
  for _ in [0:plan.samples] do
    samples := samples.push (← oneSample)
  IO.eprintln s!"clusters counted: {← totalClusters.get}"
  return samples.toList

/-- The child process: builds the input of `kind`, times `clusterCount` on it when given one,
and prints its measurement line. -/
def measureChild (clusterCount : Option (String → Nat)) (kind : InputKind) : IO Unit := do
  let input := Bench.input fixedSeed kind
  -- Printing the size makes the baseline child build the whole text, as the others do.
  IO.eprintln s!"{input.name}: {input.text.utf8ByteSize} bytes"
  let samples ← match clusterCount with
    | some count => timeSamples count input.text (timingPlan kind)
    | none => pure []
  IO.println (encodeMeasurement (← peakResidentKb) samples)

/-- Runs this executable as `measure <library> <input>` and reads its measurement line. -/
def runChild (library : Library) (kind : InputKind) : IO (Nat × List Nat) := do
  let output ← IO.Process.output
    { cmd := (← IO.appPath).toString, args := #["measure", library.name, kind.name] }
  if output.exitCode != 0 then
    throw (IO.userError
      s!"measure {library.name} {kind.name} exited with {output.exitCode}:\n{output.stderr}")
  match decodeMeasurement output.stdout with
  | some measurement => return measurement
  | none => throw (IO.userError
      s!"measure {library.name} {kind.name} printed no measurement line:\n{output.stdout}")

/-- The results row of `kind`, from one child process per library. -/
def measureRow (kind : InputKind) : IO ResultRow := do
  let (baselinePeakKb, _) ← runChild .baseline kind
  let (oursPeakKb, oursSamples) ← runChild .ours kind
  let (theirsPeakKb, theirsSamples) ← runChild .theirs kind
  return { input := kind.name, callsPerSample := (timingPlan kind).callsPerSample,
           ours := summarize oursSamples, theirs := summarize theirsSamples,
           baselinePeakKb, oursPeakKb, theirsPeakKb }

/-- The value of environment variable `name`, which the CI job must set. -/
def requiredEnv (name : String) : IO String := do
  match ← IO.getEnv name with
  | some value => return value
  | none => throw (IO.userError s!"environment variable {name} is not set")

/-- The run's metadata, which the CI job passes in environment variables. -/
def runMetaFromEnv : IO RunMeta := do
  return { machine := ← requiredEnv "BENCH_MACHINE",
           toolchain := ← requiredEnv "BENCH_TOOLCHAIN",
           oursCommit := ← requiredEnv "BENCH_OURS_COMMIT",
           theirsCommit := ← requiredEnv "BENCH_THEIRS_COMMIT" }

end Bench
